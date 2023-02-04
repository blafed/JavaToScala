package uk.co.transputersystems.transputer.simulator

import uk.co.transputersystems.transputer.simulator.debugger.DebuggerRecordedState
import uk.co.transputersystems.transputer.simulator.debugger.Process
import uk.co.transputersystems.transputer.simulator.debugger.ProcessStatus
import uk.co.transputersystems.transputer.simulator.models._
import java.io._
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.util.List
import java.util.Scanner
import uk.co.transputersystems.transputer.simulator.models.Priority.HIGH
import uk.co.transputersystems.transputer.simulator.models.Priority.LOW
import Transputer._
//remove if not needed
import scala.collection.JavaConversions._

object Transputer {

  def switchStep(transputers: Array[Transputer], stdout: PrintWriter) {
    var i: Int = 0
    var j: Int = 0
    i = 0
    while (i < transputers.length) {
      if (transputers(i).outputLink.hasData) {
        val targetChannel = transputers(i).outputLink.outChannel
        val targetProcessor = (targetChannel >> (TransputerConstants.SHIFT_IN_PORTS + 1))
        val targetPort = ((targetChannel >> 1) & ((1 << TransputerConstants.SHIFT_IN_PORTS) - 1)).toByte
        stdout.printf("Switch passed information from transputer %d to %d port %d\n", i, targetProcessor, 
          targetPort)
        transputers(targetProcessor).inputLinks(targetPort).pendingData = transputers(i).outputLink.outData
        transputers(targetProcessor).inputLinks(targetPort).hasData = true
        transputers(i).outputLink.hasData = false
      }
      j = 0
      while (j < TransputerConstants.IN_PORTS) {
        if (transputers(i).inputLinks(j).ack == TransputerConstants.ACKDATA) {
          val sourceChannel = transputers(i).inputLinks(j).inChannel
          val sourceProcessor = (sourceChannel >> (TransputerConstants.SHIFT_IN_PORTS + 1))
          transputers(sourceProcessor).outputLink.ack = TransputerConstants.ACKDATA
          transputers(i).inputLinks(j).ack = TransputerConstants.NOIO
        }
        j += 1
      }
      i += 1
    }
  }

  /**
   * @return the nth word after base
   */
  private def AtWord(base: Int, nth: Int): Int = {
    TransputerHelpers.extractWordSelector(base) + nth * TransputerConstants.BYTESPERWORD
  }

  /**
   * @return the nth byte after base
   */
  private def atByte(base: Int, nth: Int): Int = base + nth

  private def CalcShiftUp(SB: Int, DB: Int): Int = {
    val shift = (DB - SB) % TransputerConstants.BYTESPERWORD
    if (shift < 0) {
      shift + TransputerConstants.BYTESPERWORD
    } else {
      shift
    }
  }

  def ChanOffset(`val`: Int): Int = `val` >> TransputerConstants.BYTESELLEN

  /**
   * @return true if T2 is later than T1, otherwise false
   */
  private def Later(T1: Int, T2: Int): Boolean = (T1 - T2) > 0

  private def Select(P: Int, C: Int, shift_up: Int): Int = {
    val shift_up_bits = shift_up * 8
    val complement = TransputerConstants.BITSPERWORD - shift_up_bits
    val low = TransputerHelpers.shiftRight(P, complement) | TransputerHelpers.shiftLeft((-1), shift_up_bits)
    var high = C | TransputerHelpers.shiftLeft((-1), complement)
    high = TransputerHelpers.shiftLeft(high, shift_up_bits) | 
      ~(TransputerHelpers.shiftLeft((-1), shift_up_bits))
    low & high
  }
}

class Transputer(val id: Byte, val stdout: PrintWriter, val stderr: PrintWriter)
    {

  val registers = new Registers()

  private val sreg = new StatusRegister()

  private val FptrReg = new Array[Int](2)

  private val BptrReg = new Array[Int](2)

  private var Ereg: Int = _

  private val ClockReg = new Array[Int](2)

  private val mem = new Array[Byte](TransputerConstants.MEMSIZE)

  var programEndPtr: Int = _

  private val TNextReg = new Array[Int](2)

  private val TEnabled = new Array[Boolean](2)

  private var BMbuffer: Int = _

  val inputLinks = new Array[InputLink](TransputerConstants.IN_PORTS)

  private val outputLink = new OutputLink()

  val debuggerState = new DebuggerRecordedState()

  /**
   * Reads a word from an array in transputer memory
   * @param base A pointer to the start of the array
   * @param nth The array index
   * @return The word that was read
   */
  private def RIndexWord(base: Int, nth: Int): Int = {
    val bb = ByteBuffer.wrap(mem, AtWord(base, nth), TransputerConstants.BYTESPERWORD)
    bb.order(ByteOrder.LITTLE_ENDIAN)
    bb.getInt
  }

  /**
   * Reads a byte from an array in tranputer memory
   * @param base A pointer to the start of the array
   * @param nth The array index
   * @return The byte that was read
   */
  private def RIndexByte(base: Int, nth: Int): Byte = mem(atByte(base, nth))

  /**
   * Writes a word to an array in transputer memory
   * @param base A pointer to the start of the array
   * @param nth The array index
   */
  private def WIndexWord(base: Int, nth: Int, x: Int) {
    val bb = ByteBuffer.wrap(mem, AtWord(base, nth), TransputerConstants.BYTESPERWORD)
    bb.order(ByteOrder.LITTLE_ENDIAN)
    bb.putInt(x)
    debuggerState.memAccessed.add(base)
    debuggerState.memAccessed.add(base + 1)
    debuggerState.memAccessed.add(base + 2)
    debuggerState.memAccessed.add(base + 3)
  }

  /**
   * Writes a byte to an array in transputer memory
   * @param base A pointer to the start of the array
   * @param nth The array index
   */
  private def WIndexByte(base: Int, nth: Int, x: Byte) {
    mem(base + nth) = x
    debuggerState.memAccessed.add(base + nth)
  }

  private def saveRegistersPendingSoftIO() {
    WIndexWord(registers.Breg, 0, registers.Wptr)
    WIndexWord(registers.Wptr, TransputerConstants.IPTR_S, registers.Iptr + 1)
    WIndexWord(registers.Wptr, TransputerConstants.POINTER_S, registers.Creg)
  }

  FptrReg(0) = TransputerConstants.NOTPROCESS_P

  FptrReg(1) = TransputerConstants.NOTPROCESS_P

  BptrReg(0) = TransputerConstants.NOTPROCESS_P

  BptrReg(1) = TransputerConstants.NOTPROCESS_P

  registers.Wptr = TransputerConstants.NOTPROCESS_P

  var i: Int = 0

  i = 0
  while (i < TransputerConstants.IN_PORTS) {
    inputLinks(i) = new InputLink()
    inputLinks(i).fromProcessor = TransputerConstants.NOIO
    inputLinks(i).toProcessor = TransputerConstants.NOIO
    inputLinks(i).hasData = false
    inputLinks(i).ready = false
    inputLinks(i).requested = false
    inputLinks(i).enabled = false
    inputLinks(i).ack = TransputerConstants.NOIO
    i += 1
  }

  outputLink.fromProcessor = TransputerConstants.NOIO

  outputLink.toProcessor = TransputerConstants.NOIO

  outputLink.hasData = false

  outputLink.requested = false

  outputLink.ready = true

  outputLink.ack = TransputerConstants.NOIO

  outputLink.FptrReg = TransputerConstants.NOTPROCESS_P

  outputLink.BptrReg = TransputerConstants.NOTPROCESS_P

  def printRegisters(output: PrintWriter) {
    output.printf("ID: %d \tAreg: %08X \tBreg: %08X \tCreg: %08X\n\t\tOreg: %08X \tWptr: %08X \tIptr: %08X \tPriority: %01X\n\n", 
      id, registers.Areg, registers.Breg, registers.Creg, registers.Oreg, TransputerHelpers.extractWorkspacePointer(registers.Wptr), 
      registers.Iptr, TransputerHelpers.extractPriorityBit(registers.Wptr))
  }

  def printMemory(numberUnits: Int, 
      bytesPerUnit: Int, 
      format: String, 
      address: Int, 
      output: PrintWriter) {
    output.printf("## Transputer %d\n", id)
    for (unitSelector <- 0 until numberUnits) {
      var unit = 0
      for (byteSelector <- 0 until bytesPerUnit) {
        unit |= (mem(address + (unitSelector * bytesPerUnit) + byteSelector).toLong & 
          0xFF) << 
          (byteSelector * 8)
      }
      output.printf("0x%08x\t", address + (unitSelector * bytesPerUnit))
      format match {
        case "x" => output.printf("%0" + bytesPerUnit * 2 + "x", unit)
        case "d" => output.printf("%d", unit)
        case "o" => output.printf("o%o", unit)
        case "a" => output.printf("addr %08x", unit)
        case "c" => output.printf("%c", unit.toChar)
        case "f" => output.printf("%f", unit.toFloat)
        case "i" => output.printf("%2x", unit)
        case _ => output.printf("%08x", unit)
      }
      output.println()
    }
    output.printf("\n")
  }

  def printRecentMemory(output: PrintWriter) {
    var i: Int = 0
    output.printf("## Transputer %d\n", id)
    output.printf("%-12s    +3 +2 +1 +0\n", "Address")
    i = 0
    while (i < TransputerConstants.MEMSIZE) {
      if (debuggerState.memAccessed.contains(i) || debuggerState.memAccessed.contains(i + 1) || 
        debuggerState.memAccessed.contains(i + 2) || 
        debuggerState.memAccessed.contains(i + 3)) {
        output.printf("0d%04d/0x%03X    %02X %02X %02X %02X\n", i, i, mem(i + 3), mem(i + 2), mem(i + 1), 
          mem(i))
        debuggerState.memAccessed.remove(i)
        debuggerState.memAccessed.remove(i + 1)
        debuggerState.memAccessed.remove(i + 2)
        debuggerState.memAccessed.remove(i + 3)
      }
      i += 4
    }
    output.printf("\n")
  }

  def printWorkspaceMemory(output: PrintWriter) {
    output.printf("## Transputer %d\n", id)
    for (process <- debuggerState.processes) {
      output.printf("### Process %08X - %s\n", process.getCurrentWptr, process.status.name())
      val wptrs = process.getWptrs
      var i = AtWord(process.getTopWptr, 0)
      while (i <= AtWord(wptrs.get(0), 0)) {
        if (wptrs.contains(i) || wptrs.contains(i | 1)) {
          output.printf("-- Workspace %d --\n", wptrs.indexOf(i))
        }
        output.printf("0d%04d/0x%03X    %02X %02X %02X %02X\n", i, i, mem(i + 3), mem(i + 2), mem(i + 1), 
          mem(i))
        i += 4
      }
      output.printf("\n")
    }
    output.printf("\n")
  }

  def printLinks(output: PrintWriter) {
    var i: Int = 0
    i = 0
    while (i < TransputerConstants.IN_PORTS) {
      output.printf("l:%d Wptr:%08X WptrToProcessor:%08X messageLength:%d messagePointer:%08X fromProcessor:%d,toProcessor:%d,hasData:%b,pendingData:%08X,pointer:%08X,count:%08X,inChannel:%08X,readData:%08X,ready:%b,requested:%b,enabled:%b,ack:%d\n", 
        i, inputLinks(i).Wptr, inputLinks(i).WptrToProcessor, inputLinks(i).messageLength, inputLinks(i).messagePointer, 
        inputLinks(i).fromProcessor, inputLinks(i).toProcessor, inputLinks(i).hasData, inputLinks(i).pendingData, 
        inputLinks(i).pointer, inputLinks(i).count, inputLinks(i).inChannel, inputLinks(i).readData, 
        inputLinks(i).ready, inputLinks(i).requested, inputLinks(i).enabled, inputLinks(i).ack)
      i += 1
    }
    output.printf("ol:Wptr:%08X WptrToProcessor:%08X messageLength:%d FptrReg:%08X BptrReg:%08X fromProcessor:%d toProcessor:%d hasData:%b outData:%08X outPointer:%08X outCount:%08X outChannel:%08X outByte:%08X ready:%b requested:%b enabled:%b ack:%b\n", 
      outputLink.Wptr, outputLink.WptrToProcessor, outputLink.messageLength, outputLink.FptrReg, outputLink.BptrReg, 
      outputLink.fromProcessor, outputLink.toProcessor, outputLink.hasData, outputLink.outData, outputLink.outPointer, 
      outputLink.outCount, outputLink.outChannel, outputLink.outByte, outputLink.ready, outputLink.requested, 
      outputLink.enabled, outputLink.ack)
  }

  /**
   * Loads a program from a file into memory
   * @throws FileNotFoundException
   * @throws IOException
   */
  def loadProgram(fp: File): Int = {
    if (!fp.exists()) {
      return TransputerConstants.ERROR
    }
    var instruction: Byte = 0
    var i = TransputerConstants.CODESTART
    val fInput = new FileInputStream(fp)
    val fScanner = new Scanner(fInput)
    fScanner.next("Start")
    fScanner.next("address:")
    if (!fScanner.hasNextInt(16)) {
      stderr.printf("## Transputer %d\n", id)
      stderr.printf("Error reading start address\n")
      return TransputerConstants.ERROR
    } else {
      val initPointer = fScanner.nextInt(16)
      if (!fScanner.hasNext) {
        stderr.printf("## Transputer %d\n", id)
        stderr.printf("Error reading start address value\n")
        return TransputerConstants.ERROR
      } else {
        registers.Iptr = TransputerConstants.CODESTART + initPointer
      }
    }
    while (fScanner.hasNextInt(16)) {
      instruction = fScanner.nextInt(16).toByte
      mem(i) = instruction
      debuggerState.memAccessed.add(i += 1)
    }
    programEndPtr = i - 1
    registers.Wptr = TransputerHelpers.makeWorkspaceDescriptor(TransputerConstants.CODESTART - TransputerConstants.BYTESPERWORD, 
      LOW)
    debuggerState.processes.add(new Process(registers.Wptr, ProcessStatus.RUNNING))
    WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.WDESCINTSAVE, TransputerConstants.NOTPROCESS_P)
    WIndexWord(TransputerConstants.TIMERBASE, 0, TransputerConstants.NOTPROCESS_P)
    WIndexWord(TransputerConstants.TIMERBASE, 1, TransputerConstants.NOTPROCESS_P)
    fInput.close()
    TransputerConstants.SUCCESS
  }

  /**
   * Perform an overflow check
   */
  private def overflowCheck(opcode: Byte, a: Int, b: Int) {
    if (opcode == TransputerConstants.SUB) {
      opcode = TransputerConstants.ADD
      b = -b
    }
    if (opcode == TransputerConstants.ADD) {
      if (a > 0 && b > TransputerConstants.MAXINT - a) {
        sreg.errorFlag = true
      } else if (a < 0 && b < TransputerConstants.MININT - a) {
        sreg.errorFlag = true
      }
    } else if (opcode == TransputerConstants.MUL) {
      val x = a * b
      if (a != 0 && x / a != b) {
        sreg.errorFlag = true
      }
    } else {
      stderr.printf("Unrecognised opcode %X for overflow check\n", opcode)
      throw new UnexpectedOverflowException()
    }
  }

  private def setErrorFlag() {
    sreg.errorFlag = true
  }

  private def blockMoveFinalStep() {
    stdout.printf("Block_move_final_step\n")
    if (sreg.ioBit) {
      sreg.moveBit = false
      sreg.ioBit = false
      runProcess(Ereg)
    } else {
      sreg.moveBit = false
    }
  }

  /**
   * Areg - length, Breg - destination, Creg - source
   */
  private def blockMoveMiddleStep() {
    stdout.printf("Block_move_middle_step\n")
    if (registers.Areg == 0) {
      blockMoveFinalStep()
    } else {
      val SB = TransputerHelpers.extractByteSelector(registers.Creg)
      val DB = TransputerHelpers.extractByteSelector(registers.Breg)
      val shift = CalcShiftUp(SB, DB)
      var current = 0
      if (registers.Areg > shift) {
        current = if (shift == 0) RIndexWord(registers.Creg, 0) else RIndexWord(registers.Creg, 1)
      }
      val selected = Select(BMbuffer, current, shift)
      val bytesToWrite = TransputerHelpers.min((TransputerConstants.BITSPERWORD / 8) - DB, registers.Areg)
      writePartWord(registers.Breg, selected, DB, bytesToWrite)
      registers.Breg = atByte(registers.Breg, bytesToWrite)
      registers.Areg = registers.Areg - bytesToWrite
      registers.Creg = atByte(registers.Creg, bytesToWrite)
      BMbuffer = current
    }
  }

  private def writePartWord(address: Int, 
      word: Int, 
      startByte: Int, 
      len: Int) {
    var insert = 0
    for (byteIndex <- startByte until startByte + len) {
      insert = insert | TransputerHelpers.shiftLeft(0xFF, (byteIndex * 8))
    }
    val keep = ~insert
    var buffer = RIndexWord(address, 0)
    buffer = (buffer & keep) | (word & insert)
    WIndexWord(address, 0, buffer)
  }

  /**
   * Areg - length, Breg - destination, Creg - source
   */
  private def blockMoveFirstStep() {
    stdout.printf("move_first_step=> src:%08X dest:%08X len:%08X\n", registers.Creg, registers.Breg, 
      registers.Areg)
    if (registers.Areg == 0) {
      blockMoveFinalStep()
    } else {
      sreg.moveBit = true
      val SB = TransputerHelpers.extractByteSelector(registers.Creg)
      val DB = TransputerHelpers.extractByteSelector(registers.Breg)
      val shift = CalcShiftUp(SB, DB)
      var current = RIndexWord(registers.Creg, 0)
      val bytesToRead = TransputerHelpers.min((TransputerConstants.BITSPERWORD / 8) - SB, registers.Areg)
      val bytesToWrite = TransputerHelpers.min((TransputerConstants.BITSPERWORD / 8) - DB, registers.Areg)
      var selected: Int = 0
      if (bytesToRead >= bytesToWrite) {
        selected = Select(current, current, shift)
      } else {
        BMbuffer = current
        current = RIndexWord(registers.Creg, 1)
        selected = Select(BMbuffer, current, shift)
      }
      writePartWord(registers.Breg, selected, DB, bytesToWrite)
      registers.Breg = atByte(registers.Breg, bytesToWrite)
      registers.Areg = registers.Areg - bytesToWrite
      registers.Creg = atByte(registers.Creg, bytesToWrite)
      BMbuffer = current
    }
  }

  /**
   * Enqueues a process into the round-robin list of processes
   * @param Wptr a pointer to the enqueued process' workspace
   * @param processPriority the enqueued process' priority
   */
  private def enqueueProcess(Wptr: Int, processPriority: Priority) {
    val processPriorityBit = TransputerHelpers.priorityToBit(processPriority)
    if (FptrReg(processPriorityBit) == TransputerConstants.NOTPROCESS_P) {
      FptrReg(processPriorityBit) = Wptr
    } else {
      WIndexWord(BptrReg(processPriorityBit), TransputerConstants.LINK_S, Wptr)
    }
    BptrReg(processPriorityBit) = Wptr

    debuggerState.processes.stream.filter((p) => p.getCurrentWptr eq Wptr).filter((p) => p.status ne ProcessStatus.QUEUED).forEach((p) => p.status = ProcessStatus.QUEUED)

  }

  /**
   * Activates a process, i.e. loads the instruction pointer from memory
   */
  private def activateProcess() {
    registers.Oreg = 0
    registers.Iptr = RIndexWord(registers.Wptr, TransputerConstants.IPTR_S)

    debuggerState.processes.stream.filter((p) => p.getCurrentWptr eq registers.Wptr).filter((p) => p.status eq ProcessStatus.QUEUED).forEach((p) => p.status = ProcessStatus.RUNNING)
  }

  private def hardChannelInputAction(channelNumber: Int) {
    val portNumber = TransputerHelpers.convertChannelToPort(channelNumber)
    WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.IPTR_S, 
      registers.Iptr)
    inputLinks(portNumber).fromProcessor = TransputerConstants.PERFORMIO
    inputLinks(portNumber).messagePointer = registers.Creg
    inputLinks(portNumber).messageLength = registers.Areg
    inputLinks(portNumber).Wptr = registers.Wptr
    inputLinks(portNumber).inChannel = channelNumber
  }

  private def hardChannelOutputAction() {
    WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.IPTR_S, 
      registers.Iptr)
    WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.POINTER_S, 
      registers.Creg)
    WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.LENGTH_S, 
      registers.Areg)
    WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.CHAN_S, 
      registers.Breg)
    WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.LINK_S, 
      TransputerConstants.NOTPROCESS_P)
    outputLink.Wptr = registers.Wptr
    outputLink.fromProcessor = TransputerConstants.PERFORMIO
  }

  private def performInput() {
    val channelNumber = registers.Breg
    if ((channelNumber & 1) == 0) {
      stdout.printf("channelNumber >= LINKCHANS\n")
      val processDescriptor = RIndexWord(registers.Breg, 0)
      if (processDescriptor == TransputerConstants.NOTPROCESS_P) {
        stdout.printf("processDescriptor == NOTPROCESS_P\n")
        saveRegistersPendingSoftIO()
        sreg.gotoStartNewProcess = true
      } else {
        registers.Iptr += 1
        stdout.printf("ready to transfer\n")
        WIndexWord(registers.Breg, 0, TransputerConstants.NOTPROCESS_P)
        val processPointer = TransputerHelpers.extractWorkspacePointer(processDescriptor)
        val sourcePtr = TransputerHelpers.extractWorkspacePointer(RIndexWord(processPointer, TransputerConstants.POINTER_S))
        Ereg = processDescriptor
        registers.Breg = registers.Creg
        registers.Creg = sourcePtr
        sreg.moveBit = true
        sreg.ioBit = true
        blockMoveFirstStep()
      }
    } else {
      registers.Iptr += 1
      hardChannelInputAction(channelNumber)
      sreg.gotoStartNewProcess = true
    }
  }

  private def performOutput() {
    val channelNumber = registers.Breg
    if ((channelNumber & 1) == 0) {
      val processDescriptor = RIndexWord(registers.Breg, 0)
      if (processDescriptor == TransputerConstants.NOTPROCESS_P) {
        saveRegistersPendingSoftIO()
        sreg.gotoStartNewProcess = true
      } else {
        val processPointer = TransputerHelpers.extractWorkspacePointer(processDescriptor)
        val destinationPointer = RIndexWord(processPointer, TransputerConstants.POINTER_S)
        if (destinationPointer == TransputerConstants.ENABLING_P) {
          WIndexWord(processPointer, TransputerConstants.POINTER_S, TransputerConstants.READY_P)
          saveRegistersPendingSoftIO()
          sreg.gotoStartNewProcess = true
        } else if (destinationPointer == TransputerConstants.WAITING_P) {
          WIndexWord(processPointer, TransputerConstants.POINTER_S, TransputerConstants.READY_P)
          saveRegistersPendingSoftIO()
          sreg.gotoStartNewProcess = true
          registers.Iptr += 1
          runProcess(processDescriptor)
        } else if (destinationPointer == TransputerConstants.READY_P) {
          saveRegistersPendingSoftIO()
          sreg.gotoStartNewProcess = true
        } else {
          registers.Iptr += 1
          WIndexWord(registers.Breg, 0, TransputerConstants.NOTPROCESS_P)
          Ereg = processDescriptor
          registers.Breg = destinationPointer
          sreg.moveBit = true
          sreg.ioBit = true
          blockMoveFirstStep()
        }
      }
    } else {
      registers.Iptr += 1
      hardChannelOutputAction()
      sreg.gotoStartNewProcess = true
    }
  }

  private def saveRegisters() {
    WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.WDESCINTSAVE, registers.Wptr)
    if (TransputerHelpers.extractPriority(registers.Wptr) == LOW) {
      WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.IPTRINTSAVE, registers.Iptr)
      WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.AREGINTSAVE, registers.Areg)
      WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.BREGINTSAVE, registers.Breg)
      WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.CREGINTSAVE, registers.Creg)
      WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.STATUSINTSAVE, if (sreg.errorFlag) 1 else 0)
    }
    if (sreg.moveBit) {
      WIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.EREGINTSAVE, Ereg)
    }
  }

  /**
   * Runs a process
   * @param Wptr a pointer to the process workspace
   */
  private def runProcess(Wptr: Int) {
    val newProcessPriority = TransputerHelpers.extractPriority(Wptr)
    val currentProcessPriority = TransputerHelpers.extractPriority(registers.Wptr)
    val processPointer = TransputerHelpers.extractWorkspacePointer(Wptr)
    stdout.printf("run_proc\n")
    currentProcessPriority match {
      case HIGH => 
        stdout.printf("run_proc.enqueue_pri0\n")
        enqueueProcess(processPointer, newProcessPriority)
        debuggerState.processes.add(new Process(Wptr, ProcessStatus.QUEUED))

      case LOW => newProcessPriority match {
        case HIGH => 
          stdout.printf("run_proc changing priority\n")
          saveRegisters()
          registers.Wptr = Wptr
          activateProcess()
          debuggerState.processes.add(new Process(registers.Wptr, ProcessStatus.RUNNING))

        case LOW => 
          stdout.printf("run_proc.proc_pri==1\n")
          if (TransputerHelpers.extractWorkspacePointer(registers.Wptr) == 
            TransputerConstants.NOTPROCESS_P) {
            stdout.printf("run_proc-.No proc running\n")
            registers.Wptr = Wptr
            activateProcess()
            debuggerState.processes.add(new Process(Wptr, ProcessStatus.RUNNING))
          } else {
            stdout.printf("runproc.enqueue_pri1\n")
            enqueueProcess(processPointer, LOW)
            debuggerState.processes.add(new Process(Wptr, ProcessStatus.QUEUED))
          }

      }
    }
  }

  private def dequeueProcess(processPriority: Priority) {
    debuggerState.processes.stream.filter((p) => p.getCurrentWptr eq registers.Wptr).findFirst.get.status = ProcessStatus.TERMINATED

    val processPriorityBit = TransputerHelpers.priorityToBit(processPriority)
    registers.Wptr = FptrReg(processPriorityBit) | processPriorityBit
    FptrReg(processPriorityBit) = if (FptrReg(processPriorityBit) == BptrReg(processPriorityBit)) TransputerConstants.NOTPROCESS_P else RIndexWord(FptrReg(processPriorityBit), 
      TransputerConstants.LINK_S)
  }

  private def restoreRegisters() {
    stdout.printf("restore_registers\n")
    registers.Wptr = RIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.WDESCINTSAVE)
    if (registers.Wptr != (TransputerConstants.NOTPROCESS_P | 1)) {
      registers.Iptr = RIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.IPTRINTSAVE)
      registers.Areg = RIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.AREGINTSAVE)
      registers.Breg = RIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.BREGINTSAVE)
      registers.Creg = RIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.CREGINTSAVE)
      sreg.errorFlag = RIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.STATUSINTSAVE) != 
        0
    }
    if (sreg.moveBit) {
      Ereg = RIndexWord(TransputerConstants.SAVEBASE, TransputerConstants.EREGINTSAVE)
    }
  }

  private def startNewProcess() {
    sreg.gotoStartNewProcess = false
    val currentProcessPriority = TransputerHelpers.extractPriority(registers.Wptr)
    currentProcessPriority match {
      case HIGH => 
        stdout.printf("priority 0\n")
        if (FptrReg(0) != TransputerConstants.NOTPROCESS_P) {
          stdout.printf("!=NOTPROCESS_P\n")
          dequeueProcess(HIGH)
          activateProcess()
        } else {
          stdout.printf("NOTPROCESS_P\n")
          restoreRegisters()
          if (TransputerHelpers.extractWorkspacePointer(registers.Wptr) == 
            TransputerConstants.NOTPROCESS_P && 
            FptrReg(1) != TransputerConstants.NOTPROCESS_P) {
            stdout.printf("no interrupted process\n")
            dequeueProcess(LOW)
            activateProcess()
          } else if (TransputerHelpers.extractWorkspacePointer(registers.Wptr) == 
            TransputerConstants.NOTPROCESS_P) {
          } else if (sreg.moveBit) {
            blockMoveFirstStep()
          }
        }

      case LOW => 
        stdout.printf("priority 1\n")
        if (FptrReg(1) != TransputerConstants.NOTPROCESS_P) {
          dequeueProcess(LOW)
          activateProcess()
        } else {
          stdout.printf("Wptr = NOTPROCESS_P\n")
          registers.Wptr = TransputerConstants.NOTPROCESS_P | 1
        }

    }
  }

  /**
   * TODO: is 'sel' 'selected'?
   */
  private def isThisSelProcess() {
    val disableStat = RIndexWord(registers.Wptr, 0)
    stdout.printf("is_this_sel_proc\n")
    if (disableStat == TransputerConstants.NONESELECTED_O) {
      stdout.printf("Noneselected\n")
      WIndexWord(registers.Wptr, 0, registers.Areg)
      registers.Areg = 1
    } else {
      stdout.printf("else\n")
      registers.Areg = 0
    }
  }

  private def enqueueLinkOut(processPointer: Int) {
    if (outputLink.FptrReg == TransputerConstants.NOTPROCESS_P) {
      outputLink.FptrReg = processPointer
    } else {
      WIndexWord(TransputerHelpers.extractWorkspacePointer(outputLink.BptrReg), TransputerConstants.LINK_S, 
        processPointer)
    }
    outputLink.BptrReg = processPointer
  }

  private def dequeueLinkOut() {
    outputLink.WptrPrivate = outputLink.FptrReg
    outputLink.FptrReg = if (outputLink.FptrReg == outputLink.BptrReg) TransputerConstants.NOTPROCESS_P else RIndexWord(TransputerHelpers.extractWorkspacePointer(outputLink.FptrReg), 
      TransputerConstants.LINK_S)
    outputLink.outPointer = RIndexWord(TransputerHelpers.extractWorkspacePointer(outputLink.WptrPrivate), 
      TransputerConstants.POINTER_S)
    outputLink.outCount = RIndexWord(TransputerHelpers.extractWorkspacePointer(outputLink.WptrPrivate), 
      TransputerConstants.LENGTH_S)
    outputLink.outChannel = RIndexWord(TransputerHelpers.extractWorkspacePointer(outputLink.WptrPrivate), 
      TransputerConstants.CHAN_S)
    outputLink.requested = true
  }

  def processInputLink(inputLink: InputLink) {
    val token = inputLink.fromProcessor
    if (inputLink.hasData) {
      inputLink.hasData = false
      inputLink.readData = inputLink.pendingData
      inputLink.ready = true
    } else if (token != TransputerConstants.NOIO) {
      inputLink.fromProcessor = TransputerConstants.NOIO
      if (token == TransputerConstants.ENABLE) {
        inputLink.enabled = true
      } else if (token == TransputerConstants.STATUSENQUIRY) {
        inputLink.enabled = false
        inputLink.toProcessor = if (inputLink.ready) TransputerConstants.READYREQUEST else TransputerConstants.READYFALSE
      } else if (token == TransputerConstants.PERFORMIO) {
        inputLink.pointer = inputLink.messagePointer
        inputLink.count = inputLink.messageLength
        inputLink.requested = true
      } else if (token == TransputerConstants.RESETREQUEST) {
        inputLink.ready = false
        inputLink.enabled = false
        inputLink.requested = false
        inputLink.toProcessor = TransputerConstants.ACKRESET
      }
    } else if (inputLink.requested && inputLink.ready) {
      inputLink.ack = TransputerConstants.ACKDATA
      WIndexByte(inputLink.pointer, 0, inputLink.readData)
      inputLink.pointer = atByte(inputLink.pointer, 1)
      inputLink.count = inputLink.count - 1
      if (inputLink.count == 0) {
        inputLink.requested = false
        inputLink.toProcessor = TransputerConstants.RUNREQUEST
        inputLink.WptrToProcessor = inputLink.Wptr
        var interaction: Int = 0
        interaction = inputLink.fromProcessor
        while (interaction == TransputerConstants.NOIO) {
          interaction = inputLink.fromProcessor
          performStep()
        }
        inputLink.fromProcessor = TransputerConstants.NOIO
        if (interaction == TransputerConstants.ACKRUN) {
        } else if (interaction == TransputerConstants.RESETREQUEST) {
        }
      } else {
      }
      inputLink.ready = false
    } else if (inputLink.enabled && inputLink.ready) {
      inputLink.enabled = false
      inputLink.toProcessor = TransputerConstants.READYREQUEST
      inputLink.WptrToProcessor = inputLink.Wptr
      var interaction = TransputerConstants.NOIO
      while (interaction == TransputerConstants.NOIO) {
        interaction = inputLink.fromProcessor
        performStep()
      }
      inputLink.fromProcessor = TransputerConstants.NOIO
      if (interaction == TransputerConstants.ACKREADY) {
      } else if (interaction == TransputerConstants.STATUSENQUIRY) {
      } else if (interaction == TransputerConstants.RESETREQUEST) {
        inputLink.ready = false
      }
    }
  }

  def processOutputLink() {
    var token: Int = 0
    token = outputLink.fromProcessor
    outputLink.fromProcessor = TransputerConstants.NOIO
    if (token == TransputerConstants.PERFORMIO) {
      val processPointer = outputLink.Wptr
      if (!(outputLink.ready) || outputLink.requested || 
        outputLink.FptrReg != TransputerConstants.NOTPROCESS_P) {
        enqueueLinkOut(processPointer)
      } else {
        outputLink.WptrPrivate = processPointer
        outputLink.outPointer = RIndexWord(TransputerHelpers.extractWorkspacePointer(processPointer), 
          TransputerConstants.POINTER_S)
        outputLink.outCount = RIndexWord(TransputerHelpers.extractWorkspacePointer(processPointer), TransputerConstants.LENGTH_S)
        outputLink.outChannel = RIndexWord(TransputerHelpers.extractWorkspacePointer(processPointer), 
          TransputerConstants.CHAN_S)
        outputLink.requested = true
      }
    } else if (token == TransputerConstants.RESETREQUEST) {
      outputLink.ready = true
      outputLink.requested = false
      outputLink.toProcessor = TransputerConstants.ACKRESET
    } else if (outputLink.ready && outputLink.requested) {
      if (outputLink.outCount == 0) {
        outputLink.requested = false
        outputLink.toProcessor = TransputerConstants.RUNREQUEST
        outputLink.WptrToProcessor = outputLink.Wptr
        var interaction: Int = 0
        interaction = outputLink.fromProcessor
        while (interaction != TransputerConstants.ACKRUN) {
          if (interaction == TransputerConstants.PERFORMIO) {
            enqueueLinkOut(outputLink.Wptr)
            outputLink.fromProcessor = TransputerConstants.NOIO
          }
          performStep()
          interaction = outputLink.fromProcessor
        }
        outputLink.fromProcessor = TransputerConstants.NOIO
      } else {
        outputLink.outByte = RIndexByte(outputLink.outPointer, 0)
        outputLink.outPointer = atByte(outputLink.outPointer, 1)
        outputLink.outCount = outputLink.outCount - 1
        outputLink.hasData = true
        outputLink.outData = outputLink.outByte
        outputLink.ready = false
      }
    } else if ((outputLink.ready) && !(outputLink.requested) && 
      (outputLink.FptrReg != TransputerConstants.NOTPROCESS_P)) {
      dequeueLinkOut()
      outputLink.requested = true
    } else if ((token = outputLink.ack) != TransputerConstants.NOIO) {
      outputLink.ack = TransputerConstants.NOIO
      outputLink.ready = true
    }
  }

  private def disableChannel() {
    if (registers.Breg != 0) {
      stdout.printf("Breg != FALSE\n")
      val channelNumber = registers.Creg
      if ((channelNumber & 1) == 0) {
        stdout.printf("Soft channel\n")
        registers.Breg = RIndexWord(registers.Creg, 0)
        if (registers.Breg == TransputerConstants.NOTPROCESS_P) {
          stdout.printf("Breg == NOTPROCESS_P\n")
          registers.Areg = 0
        } else if (registers.Breg == registers.Wptr) {
          stdout.printf("Breg == Wdescreg\n")
          WIndexWord(registers.Creg, 0, TransputerConstants.NOTPROCESS_P)
          registers.Areg = 0
        } else {
          stdout.printf("Breg else\n")
          isThisSelProcess
        }
      } else {
        var token: Int = 0
        val portNumber = TransputerHelpers.convertChannelToPort(channelNumber)
        inputLinks(portNumber).Wptr = TransputerConstants.NOTPROCESS_P
        inputLinks(portNumber).fromProcessor = TransputerConstants.STATUSENQUIRY
        token = inputLinks(portNumber).toProcessor
        while (token == TransputerConstants.NOIO) {
          token = inputLinks(portNumber).toProcessor
          processInputLink(inputLinks(portNumber))
        }
        inputLinks(portNumber).toProcessor = TransputerConstants.NOIO
        if (token == TransputerConstants.READYREQUEST) {
          isThisSelProcess
        } else if (token == TransputerConstants.READYFALSE) {
          registers.Areg = 0
        }
      }
    } else {
      registers.Areg = 0
    }
  }

  private def enableChannel() {
    if (registers.Areg != 0) {
      val channelNumber = registers.Breg
      if ((channelNumber & 1) == 0) {
        val tmp = RIndexWord(registers.Breg, 0)
        if (tmp == TransputerConstants.NOTPROCESS_P) {
          WIndexWord(registers.Breg, 0, registers.Wptr)
        } else if (tmp == registers.Wptr) {
        } else {
          WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.STATE_S, 
            TransputerConstants.READY_P)
        }
      } else {
        var token: Int = 0
        val portNumber = TransputerHelpers.convertChannelToPort(channelNumber)
        inputLinks(portNumber).fromProcessor = TransputerConstants.STATUSENQUIRY
        token = inputLinks(portNumber).toProcessor
        while (token == TransputerConstants.NOIO) {
          token = inputLinks(portNumber).toProcessor
          processInputLink(inputLinks(portNumber))
        }
        inputLinks(portNumber).toProcessor = TransputerConstants.NOIO
        if (token == TransputerConstants.READYREQUEST) {
          WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), TransputerConstants.STATE_S, 
            TransputerConstants.READY_P)
        } else if (token == TransputerConstants.READYFALSE) {
          inputLinks(portNumber).fromProcessor = TransputerConstants.ENABLE
          inputLinks(portNumber).Wptr = registers.Wptr
        }
      }
    }
    registers.Breg = registers.Creg
  }

  private def initiateWait() {
    WIndexWord(registers.Wptr, TransputerConstants.STATE_S, TransputerConstants.WAITING_P)
    WIndexWord(registers.Wptr, TransputerConstants.IPTR_S, registers.Iptr)
    registers.Iptr -= 1
    sreg.gotoStartNewProcess = true
  }

  /**
   * The first step of inserting the current process into the timer queue
   * Areg - time, Breg - previous, Creg - subsequent
   */
  private def timerQueueInsertFirstStep() {
    stdout.printf("insert_first_step\n")
    sreg.timeIns = true
    WIndexWord(registers.Wptr, TransputerConstants.STATE_S, TransputerConstants.WAITING_P)
    WIndexWord(registers.Wptr, TransputerConstants.TIME_S, registers.Areg)
    registers.Breg = AtWord(TransputerConstants.TIMERBASE, TransputerHelpers.priorityToBit(TransputerHelpers.extractPriority(registers.Wptr)))
    timerQueueInsertTest()
  }

  /**
   * Areg - time, Breg - previous, Creg - subsequent
   */
  private def timerQueueInsertMiddleStep() {
    stdout.printf("insert_middle_step\n")
    registers.Breg = AtWord(registers.Creg, TransputerConstants.TLINK_S)
    timerQueueInsertTest()
  }

  /**
   * Areg - time, Breg - previous, Creg - subsequent
   */
  private def timerQueueInsertTest() {
    stdout.printf("insert_test\n")
    registers.Creg = RIndexWord(registers.Breg, 0)
    if (registers.Creg == TransputerConstants.NOTPROCESS_P) {
      timerQueueInsertFinalStep()
    } else {
      val subsequentTime = RIndexWord(registers.Creg, TransputerConstants.TIME_S)
      val laterFlag = Later(registers.Areg, subsequentTime)
      if (!laterFlag) {
        timerQueueInsertFinalStep()
      }
    }
  }

  /**
   * Areg - time, Breg - previous, Creg - subsequent
   */
  private def timerQueueInsertFinalStep() {
    stdout.printf("insert_final_step\n")
    WIndexWord(registers.Breg, 0, TransputerHelpers.extractWorkspacePointer(registers.Wptr))
    WIndexWord(registers.Wptr, TransputerConstants.TLINK_S, registers.Creg)
    WIndexWord(registers.Wptr, TransputerConstants.IPTR_S, registers.Iptr + 1)
    registers.Breg = RIndexWord(TransputerConstants.TIMERBASE, TransputerHelpers.extractPriorityBit(registers.Wptr))
    TNextReg(TransputerHelpers.extractPriorityBit(registers.Wptr)) = RIndexWord(registers.Breg, TransputerConstants.TIME_S)
    TEnabled(TransputerHelpers.extractPriorityBit(registers.Wptr)) = true
    registers.Creg = AtWord(TransputerConstants.TIMERBASE, TransputerHelpers.extractPriorityBit(registers.Wptr))
    sreg.timeIns = false
    sreg.gotoStartNewProcess = true
  }

  /**
   * Breg - previous, Creg - subsequent
   */
  private def timerQueueDeleteFirstStep() {
    stdout.printf("delete_first_step\n")
    sreg.timeDel = true
    TEnabled(TransputerHelpers.extractPriorityBit(registers.Wptr)) = false
    registers.Breg = AtWord(TransputerConstants.TIMERBASE, TransputerHelpers.extractPriorityBit(registers.Wptr))
    timerQueueDeleteTest()
  }

  /**
   * Breg - previous, Creg - subsequent
   */
  private def timerQueueDeleteMiddleStep() {
    stdout.printf("delete_middle_step\n")
    registers.Breg = AtWord(registers.Creg, TransputerConstants.TLINK_S)
    timerQueueDeleteTest()
  }

  /**
   * Breg - previous, Creg - subsequent
   */
  private def timerQueueDeleteTest() {
    stdout.printf("delete_test\n")
    registers.Creg = RIndexWord(registers.Breg, 0)
    if (registers.Creg == 
      TransputerHelpers.extractWorkspacePointer(registers.Wptr)) {
      timerQueueDeleteFinalStep()
    }
  }

  /**
   * Breg - previous, Creg - subsequent
   */
  private def timerQueueDeleteFinalStep() {
    stdout.printf("delete_final_step\n")
    registers.Creg = RIndexWord(registers.Wptr, TransputerConstants.TLINK_S)
    WIndexWord(registers.Breg, 0, registers.Creg)
    WIndexWord(registers.Wptr, TransputerConstants.TLINK_S, TransputerConstants.TIMENOTSET_P)
    registers.Breg = RIndexWord(TransputerConstants.TIMERBASE, TransputerHelpers.extractPriorityBit(registers.Wptr))
    if (registers.Breg != TransputerConstants.NOTPROCESS_P) {
      TNextReg(TransputerHelpers.extractPriorityBit(registers.Wptr)) = RIndexWord(registers.Breg, TransputerConstants.TIME_S)
      TEnabled(TransputerHelpers.extractPriorityBit(registers.Wptr)) = true
    }
    sreg.timeDel = false
  }

  /**
   * Handle a timer request
   * @param priorityQueue The timer which has made the request
   */
  private def handleTimerRequest(priorityQueue: Priority) {
    val priorityBit = TransputerHelpers.priorityToBit(priorityQueue)
    TEnabled(priorityBit) = false
    val frontproc = RIndexWord(TransputerConstants.TIMERBASE, priorityBit)
    val secondproc = RIndexWord(frontproc, TransputerConstants.TLINK_S)
    WIndexWord(frontproc, TransputerConstants.TLINK_S, TransputerConstants.TIMESET_P)
    WIndexWord(TransputerConstants.TIMERBASE, priorityBit, secondproc)
    if (secondproc != TransputerConstants.NOTPROCESS_P) {
      stdout.printf("secondproc != NOTPROCESS_P\n")
      TNextReg(priorityBit) = RIndexWord(secondproc, TransputerConstants.TIME_S)
      TEnabled(priorityBit) = true
    }
    val status = RIndexWord(frontproc, TransputerConstants.POINTER_S)
    if (status == TransputerConstants.WAITING_P) {
      WIndexWord(frontproc, TransputerConstants.POINTER_S, TransputerConstants.READY_P)
      runProcess(TransputerHelpers.makeWorkspaceDescriptor(frontproc, priorityQueue))
    }
  }

  def handshakeInput(i: Int, token: Int) {
    while (token == TransputerConstants.NOIO) {
      token = inputLinks(i).toProcessor
      processInputLink(inputLinks(i))
    }
    inputLinks(i).toProcessor = TransputerConstants.NOIO
  }

  def handshakeOutput(token: Int) {
    while (token == TransputerConstants.NOIO) {
      token = outputLink.toProcessor
      processOutputLink()
    }
    outputLink.toProcessor = TransputerConstants.NOIO
  }

  /**
   * Execute a secondary instruction, i.e. one where the actual opcode is in the operand register
   */
  private def executeSecondaryInstruction() {
    val opcode = (registers.Oreg & 0xFF).toByte
    var tmp: Int = 0
    var laterFlag: Boolean = false
    var shift_val: Int = 0
    var op0: Int = 0
    var op1: Int = 0
    val processToUpdate: Process = null
    registers.Oreg = 0
    opcode match {
      case (TransputerConstants.REV) => 
        stdout.printf("rev\n")
        tmp = registers.Areg
        registers.Areg = registers.Breg
        registers.Breg = tmp
        registers.Iptr += 1

      case (TransputerConstants.ADD) => 
        stdout.printf("add\n")
        overflowCheck(TransputerConstants.ADD, registers.Breg, registers.Areg)
        registers.Areg = registers.Areg + registers.Breg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.SUB) => 
        stdout.printf("sub\n")
        overflowCheck(TransputerConstants.SUB, registers.Breg, registers.Areg)
        registers.Areg = registers.Breg - registers.Areg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.MUL) => 
        stdout.printf("mul\n")
        overflowCheck(TransputerConstants.MUL, registers.Breg, registers.Areg)
        registers.Areg = registers.Breg * registers.Areg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.DIV) => 
        stdout.printf("div\n")
        if ((registers.Breg == TransputerConstants.MININT && registers.Areg == -1) || 
          registers.Areg == 0) {
          setErrorFlag()
        } else {
          registers.Areg = registers.Breg / registers.Areg
        }
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.DIFF) => 
        stdout.printf("diff\n")
        registers.Areg = (registers.Breg - registers.Areg)
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.SUM) => 
        stdout.printf("sum\n")
        registers.Areg = registers.Breg + registers.Areg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.AND) => 
        stdout.printf("and\n")
        registers.Areg = registers.Areg & registers.Breg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.OR) => 
        stdout.printf("or\n")
        registers.Areg = registers.Areg | registers.Breg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.XOR) => 
        stdout.printf("xor\n")
        registers.Areg = registers.Areg ^ registers.Breg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.NOT) => 
        stdout.printf("not\n")
        registers.Areg = ~registers.Areg
        registers.Iptr += 1

      case (TransputerConstants.SHL) => 
        stdout.printf("shl\n")
        shift_val = registers.Areg
        registers.Areg = if (shift_val < TransputerConstants.BITSPERWORD) registers.Breg << registers.Areg else 0
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.SHR) => 
        stdout.printf("shr\n")
        shift_val = registers.Areg
        registers.Areg = if (shift_val < TransputerConstants.BITSPERWORD) registers.Breg >> registers.Areg else 0
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.GT) => 
        stdout.printf("gt\n")
        registers.Areg = if (registers.Breg > registers.Areg) 1 else 0
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.LEND) => 
        stdout.printf("lend\n")
        registers.Creg = RIndexWord(registers.Breg, 1)
        registers.Creg = registers.Creg - 1
        WIndexWord(registers.Breg, 1, registers.Creg)
        if (registers.Creg > 0) {
          registers.Creg = RIndexWord(registers.Breg, 0)
          registers.Creg = registers.Creg + 1
          WIndexWord(registers.Breg, 0, registers.Creg)
          registers.Iptr = atByte(registers.Iptr + 1, -(registers.Areg))
        } else if (registers.Creg <= 0) {
          registers.Iptr += 1
        }

      case (TransputerConstants.BSUB) => 
        stdout.printf("bsub\n")
        registers.Areg = atByte(registers.Areg, registers.Breg)
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.WSUB) => 
        stdout.printf("wsub\n")
        registers.Areg = AtWord(registers.Areg, registers.Breg)
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.BCNT) => 
        stdout.printf("bcnt\n")
        registers.Areg = registers.Areg * TransputerConstants.BYTESPERWORD
        registers.Iptr += 1

      case (TransputerConstants.WCNT) => 
        stdout.printf("wcnt\n")
        registers.Creg = registers.Breg
        registers.Breg = TransputerHelpers.extractByteSelector(registers.Areg)
        registers.Areg = registers.Areg >> TransputerConstants.BYTESELLEN
        registers.Iptr += 1

      case (TransputerConstants.LDPI) => 
        stdout.printf("ldpi\n")
        registers.Areg = atByte(registers.Iptr + 1, registers.Areg)
        registers.Iptr += 1

      case (TransputerConstants.MOVE) => 
        stdout.printf("move\n")
        blockMoveFirstStep()
        registers.Iptr += 1

      case (TransputerConstants.GCALL) => 
        stdout.printf("gcall\n")
        tmp = registers.Areg
        registers.Areg = registers.Iptr + 1
        registers.Iptr = tmp

      case (TransputerConstants.GAJW) => 
        stdout.printf("gajw\n")

        processToUpdate = debuggerState.processes.stream.filter((p) => p.status eq ProcessStatus.RUNNING).filter((p) => p.getCurrentWptr eq registers.Wptr).findFirst.get


        tmp = TransputerHelpers.extractWorkspacePointer(registers.Wptr)
        registers.Wptr = TransputerHelpers.extractWorkspacePointer(registers.Areg) | 
          TransputerHelpers.extractPriorityBit(registers.Wptr)
        registers.Areg = tmp & 0xFFFFFFFC
        registers.Iptr += 1
        processToUpdate.updateWptr(registers.Wptr)

      case (TransputerConstants.RET) => 
        stdout.printf("ret\n")

        processToUpdate = debuggerState.processes.stream.filter((p) => p.status eq ProcessStatus.RUNNING).filter((p) => p.getCurrentWptr eq registers.Wptr).findFirst.get

        registers.Iptr = RIndexWord(registers.Wptr, 0)
        registers.Wptr = AtWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), 4) | 
          TransputerHelpers.extractPriorityBit(registers.Wptr)
        processToUpdate.updateWptr(registers.Wptr)

      case (TransputerConstants.STARTP) => 
        stdout.printf("startp\n")
        registers.Iptr += 1
        tmp = atByte(registers.Iptr, registers.Breg)
        WIndexWord(registers.Areg, TransputerConstants.IPTR_S, tmp)
        runProcess(registers.Areg | 
          TransputerHelpers.extractPriorityBit(registers.Wptr))

      case (TransputerConstants.ENDP) => 
        stdout.printf("endp\n")
        processToUpdate = debuggerState.processes.stream.filter((p) => p.status eq ProcessStatus.RUNNING).filter((p) => p.getCurrentWptr eq registers.Wptr).findFirst.get
        tmp = RIndexWord(registers.Areg, 1)
        if (tmp == 1) {
          registers.Iptr = RIndexWord(registers.Areg, 0)
          registers.Wptr = registers.Areg | 
            TransputerHelpers.extractPriorityBit(registers.Wptr)
          processToUpdate.updateWptr(registers.Wptr)
        } else {
          stdout.printf("ENDP elseA\n")
          WIndexWord(registers.Areg, 1, tmp - 1)
          sreg.gotoStartNewProcess = true
          processToUpdate.status = ProcessStatus.TERMINATED
        }

      case (TransputerConstants.RUNP) => 
        stdout.printf("runp\n")
        registers.Iptr += 1
        runProcess(registers.Areg)

      case (TransputerConstants.STOPP) => 
        stdout.printf("stopp\n")
        registers.Iptr += 1
        WIndexWord(registers.Wptr, TransputerConstants.IPTR_S, registers.Iptr)
        sreg.gotoStartNewProcess = true

      case (TransputerConstants.LDPRI) => 
        stdout.printf("ldpri\n")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = TransputerHelpers.extractPriorityBit(registers.Wptr)
        registers.Iptr += 1

      case (TransputerConstants.MINT) => 
        stdout.printf("mint\n")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = TransputerConstants.MININT
        registers.Iptr += 1

      case (TransputerConstants.ALT) => 
        stdout.printf("alt\n")
        registers.Iptr += 1
        WIndexWord(registers.Wptr, TransputerConstants.STATE_S, TransputerConstants.ENABLING_P)

      case (TransputerConstants.ALTWT) => 
        stdout.printf("altwt\n")
        registers.Iptr += 1
        WIndexWord(registers.Wptr, 0, TransputerConstants.NONESELECTED_O)
        registers.Areg = RIndexWord(registers.Wptr, TransputerConstants.STATE_S)
        if (registers.Areg == TransputerConstants.READY_P) {
        } else {
          initiateWait()
        }

      case (TransputerConstants.ALTEND) => 
        stdout.printf("altend\n")
        registers.Iptr += 1
        tmp = RIndexWord(registers.Wptr, 0)
        registers.Iptr = atByte(registers.Iptr, tmp)

      case (TransputerConstants.LDTIMER) => 
        stdout.printf("ldtimer\n")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = ClockReg(TransputerHelpers.extractPriorityBit(registers.Wptr))
        registers.Iptr += 1

      case (TransputerConstants.TIN) => 
        stdout.printf("tin\n")
        laterFlag = Later(ClockReg(TransputerHelpers.extractPriorityBit(registers.Wptr)), registers.Areg)
        if (!laterFlag) {
          registers.Areg += 1
          timerQueueInsertFirstStep()
        }

      case (TransputerConstants.TALT) => 
        stdout.printf("talt\n")
        WIndexWord(registers.Wptr, TransputerConstants.TLINK_S, TransputerConstants.TIMENOTSET_P)
        WIndexWord(registers.Wptr, TransputerConstants.STATE_S, TransputerConstants.ENABLING_P)
        registers.Iptr += 1

      case (TransputerConstants.TALTWT) => 
        stdout.printf("taltwt\n")
        registers.Iptr += 1
        WIndexWord(registers.Wptr, 0, TransputerConstants.NONESELECTED_O)
        registers.Creg = RIndexWord(registers.Wptr, TransputerConstants.STATE_S)
        if (registers.Creg == TransputerConstants.READY_P) {
          WIndexWord(registers.Wptr, TransputerConstants.TIME_S, ClockReg(TransputerHelpers.extractPriorityBit(registers.Wptr)))
        } else {
          registers.Breg = RIndexWord(registers.Wptr, TransputerConstants.TLINK_S)
          if (registers.Breg == TransputerConstants.TIMENOTSET_P) {
            initiateWait()
          } else if (registers.Breg == TransputerConstants.TIMESET_P) {
            registers.Areg = RIndexWord(registers.Wptr, TransputerConstants.TIME_S)
            laterFlag = Later(ClockReg(TransputerHelpers.extractPriorityBit(registers.Wptr)), registers.Areg)
            if (laterFlag) {
              WIndexWord(registers.Wptr, TransputerConstants.STATE_S, TransputerConstants.READY_P)
              WIndexWord(registers.Wptr, TransputerConstants.TIME_S, ClockReg(TransputerHelpers.extractPriorityBit(registers.Wptr)))
            } else {
              registers.Areg += 1
              registers.Iptr -= 1
              timerQueueInsertFirstStep()
            }
          }
        }

      case (TransputerConstants.ENBS) => stdout.printf("enbs\n")
      case (TransputerConstants.DISS) => stdout.printf("diss\n")
      case (TransputerConstants.ENBC) => 
        stdout.printf("enbc\n")
        enableChannel()
        registers.Iptr += 1

      case (TransputerConstants.DISC) => 
        stdout.printf("disc\n")
        disableChannel()
        registers.Iptr += 1

      case (TransputerConstants.ENBT) => 
        stdout.printf("enbt\n")
        if (registers.Areg != 0) {
          tmp = RIndexWord(registers.Wptr, TransputerConstants.TLINK_S)
          if (tmp == TransputerConstants.TIMENOTSET_P) {
            WIndexWord(registers.Wptr, TransputerConstants.TLINK_S, TransputerConstants.TIMESET_P)
            WIndexWord(registers.Wptr, TransputerConstants.TIME_S, registers.Breg)
          } else if (tmp == TransputerConstants.TIMESET_P) {
            tmp = RIndexWord(registers.Wptr, TransputerConstants.TIME_S)
            laterFlag = Later(tmp, registers.Breg)
            if (laterFlag) {
              WIndexWord(registers.Wptr, TransputerConstants.TIME_S, registers.Breg)
            }
          }
        } else if (registers.Areg == 0) {
        }
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.DIST) => 
        stdout.printf("dist\n")
        registers.Iptr += 1
        if (registers.Breg != 0) {
          registers.Oreg = RIndexWord(registers.Wptr, TransputerConstants.TLINK_S)
          if (registers.Oreg == TransputerConstants.TIMENOTSET_P) {
            registers.Areg = 0
          } else if (registers.Oreg == TransputerConstants.TIMESET_P) {
            registers.Oreg = RIndexWord(registers.Wptr, TransputerConstants.TIME_S)
            laterFlag = Later(registers.Oreg, registers.Creg)
            if (laterFlag) {
              isThisSelProcess
            } else {
              registers.Areg = 0
            }
          } else {
            timerQueueDeleteFirstStep()
            registers.Areg = 0
          }
        } else if (registers.Breg == 0) {
          registers.Areg = 0
        }
        registers.Oreg = 0

      case (TransputerConstants.CSUB) => 
        stdout.printf("csub\n")
        op0 = registers.Areg
        op1 = registers.Breg
        if (op1 >= op0) {
          sreg.errorFlag = true
        }
        registers.Areg = registers.Breg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.CCNT) => 
        stdout.printf("ccnt\n")
        op0 = registers.Areg
        op1 = registers.Breg
        if (op1 == 0 || op1 > op0) {
          sreg.errorFlag = true
        }
        registers.Areg = registers.Breg
        registers.Breg = registers.Creg
        registers.Iptr += 1

      case (TransputerConstants.TESTERR) => 
        stdout.printf("testerr\n")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = if (!sreg.errorFlag) 1 else 0
        sreg.errorFlag = false
        registers.Iptr += 1

      case (TransputerConstants.SETERR) => 
        stdout.printf("seterr\n")
        registers.Iptr += 1
        sreg.errorFlag = true

      case (TransputerConstants.STOPERR) => 
        stdout.printf("stoperr\n")
        registers.Iptr += 1
        if (sreg.errorFlag) {
          WIndexWord(registers.Wptr, TransputerConstants.IPTR_S, registers.Iptr)
          sreg.gotoStartNewProcess = true
        }

      case (TransputerConstants.CLRHALTERR) => 
        stdout.printf("clrhalterr\n")
        registers.Iptr += 1
        sreg.haltOnErr = false

      case (TransputerConstants.SETHALTERR) => 
        stdout.printf("sethalterr\n")
        registers.Iptr += 1
        sreg.haltOnErr = true

      case (TransputerConstants.TESTHALTERR) => 
        stdout.printf("testhalterr")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = if ((sreg.haltOnErr)) 1 else 0
        registers.Iptr += 1

      case (TransputerConstants.RESETCH) => stdout.printf("resetch\n")
      case (TransputerConstants.STHF) => stdout.printf("sthf\n")
      case (TransputerConstants.STLF) => stdout.printf("stlf\n")
      case (TransputerConstants.STTIMER) => stdout.printf("sttimer\n")
      case (TransputerConstants.STHB) => stdout.printf("sthb\n")
      case (TransputerConstants.STLB) => stdout.printf("stlb\n")
      case (TransputerConstants.SAVEH) => stdout.printf("saveh\n")
      case (TransputerConstants.SAVEL) => stdout.printf("savel\n")
      case (TransputerConstants.IN) => 
        stdout.printf("in\n")
        performInput()

      case (TransputerConstants.OUT) => 
        stdout.printf("out\n")
        performOutput()

      case (TransputerConstants.OUTWORD) => 
        stdout.printf("outword\n")
        WIndexWord(registers.Wptr, 0, registers.Areg)
        registers.Areg = TransputerConstants.BYTESPERWORD
        registers.Creg = TransputerHelpers.extractWorkspacePointer(registers.Wptr)
        performOutput()

      case _ => 
        System.err.printf("Instruction opcode '%02X' not implemented at Iptr '%08X'\n", opcode, registers.Iptr)
        System.exit(1)

    }
  }

  def printNextInstruction(output: PrintWriter) {
    printMemory(1, 1, "i", registers.Iptr, output)
  }

  def printSRegisters(output: PrintWriter) {
    output.printf("ID:%d", id)
    if (sreg.errorFlag) {
      output.printf("  ErrorFlag:TRUE")
    } else {
      output.printf("  ErrorFlag:FALSE")
    }
    if (sreg.moveBit) {
      output.printf("  MoveBit:TRUE")
    } else {
      output.printf("  MoveBit:FALSE")
    }
    if (sreg.haltOnErr) {
      output.printf("  HaltOnError:TRUE")
    } else {
      output.printf("  HaltOnError:FALSE")
    }
    if (sreg.gotoStartNewProcess) {
      output.printf("  GotoSNP:TRUE")
    } else {
      output.printf("  GotoSNP:FALSE")
    }
    if (sreg.ioBit) {
      output.printf("  IOBit:TRUE")
    } else {
      output.printf("  IOBit:FALSE")
    }
    if (sreg.timeIns) {
      output.printf("  TimeIns:TRUE")
    } else {
      output.printf("  TimeIns:FALSE")
    }
    if (sreg.timeDel) {
      output.printf("  TimeDel:TRUE")
    } else {
      output.printf("  TimeDel:FALSE")
    }
    if (sreg.distAndIns) {
      output.printf("  DistAndIns:TRUE\n")
    } else {
      output.printf("  DistAndIns:FALSE\n")
    }
  }

  def printCRegisters(output: PrintWriter) {
    output.printf("## Transputer %d\n", id)
    output.printf("==Process queue==\n")
    output.printf("%8s\t%8s\t%8s\n", "Priority", "FPtr", "BPtr")
    output.printf("%8d\t%08X\t%08X\n", 0, FptrReg(0), BptrReg(0))
    output.printf("%8d\t%08X\t%08X\n\n", 1, FptrReg(1), BptrReg(1))
    output.printf("==Process clock == ClockReg==\n")
    output.printf("%8s\t%8s\n", "Priority", "Value")
    output.printf("%8d\t%08X\n", 0, ClockReg(0))
    output.printf("%8d\t%08X\n\n", 1, ClockReg(1))
    output.printf("==Other registers==\n")
    output.printf("%12s\t%8s\t%8s\n", "Name", "Priority", "Value")
    output.printf("%12s\t%8d\t%08X\n", "TNextReg", 0, TNextReg(0))
    output.printf("%12s\t%8d\t%08X\n", "TNextReg", 1, TNextReg(1))
    output.printf("%12s\t%8d\t%08b\n", "TEnabled", 0, TEnabled(0))
    output.printf("%12s\t%8d\t%08b\n\n", "TEnabled", 1, TEnabled(1))
    output.printf("Ereg:%08X\tBMBuffer:%08X\n", Ereg, BMbuffer)
  }

  def printProcessList(output: PrintWriter) {
    output.printf("## Transputer %d\n", id)
    output.printf("ID Wptr    \t\tStatus\n")
    var i = 0
    for (process <- debuggerState.processes) {
      output.printf("%02d 0x%08X\t%s\n", i += 1, process.getCurrentWptr, process.status.name())
    }
  }

  def printBreakpoints(output: PrintWriter) {
    var i: Int = 0
    var has_breaks = false
    output.printf("## Transputer %d\n", id)
    output.printf("%8s\t%8s\t%8s\n", "Hex addr", "Dec addr", "Value")
    i = 0
    while (i < TransputerConstants.MEMSIZE) {
      if (debuggerState.breakpoints.contains(i)) {
        output.printf("%08X\t%8d\t%02X\n", i, i, mem(i))
        has_breaks = true
      }
      i += 1
    }
    if (!has_breaks) {
      output.printf("There are no set breakpoints\n")
    }
  }

  def unsetBreakpoint(addr: Int, output: PrintWriter) {
    output.printf("## Transputer %d\n", id)
    if (addr < 0 || addr >= TransputerConstants.MEMSIZE) {
      output.printf("Invalid address\n")
    } else if (!debuggerState.breakpoints.contains(addr)) {
      output.printf("No breakpoint found at Hex_addr:%08X Dec_addr:%-8d Value:%08X\n", addr, addr, mem(addr))
    } else {
      debuggerState.breakpoints.remove(addr)
      output.printf("Unset breakpoint successful\n")
    }
  }

  def setBreakpoint(addr: Int, output: PrintWriter) {
    output.printf("## Transputer %d\n", id)
    if (addr < 0 || addr >= TransputerConstants.MEMSIZE) {
      output.printf("Invalid address\n")
    } else if (debuggerState.breakpoints.contains(addr)) {
      output.printf("Breakpoint already exists at Hex_addr:%08X Dec_addr:%-8d Value:%08X\n", addr, addr, 
        mem(addr))
    } else {
      debuggerState.breakpoints.add(addr)
      output.printf("Set breakpoint successful\n")
    }
  }

  /**
   * Executes a primary instruction, i.e. an instruction which uses the operand as a parameter
   */
  private def executePrimaryInstruction() {
    val opcode = TransputerHelpers.extractOpcode(mem(registers.Iptr))
    val operand = TransputerHelpers.extractDirectOperand(mem(registers.Iptr))
    val processToUpdate: Process = null
    registers.Oreg = operand | registers.Oreg
    stdout.printf("Executed ")
    opcode match {
      case (TransputerConstants.PFIX) => 
        stdout.printf("pfix\n")
        registers.Oreg = registers.Oreg << 4
        registers.Iptr += 1

      case (TransputerConstants.NFIX) => 
        stdout.printf("nfix\n")
        registers.Oreg = (~registers.Oreg) << 4
        registers.Iptr += 1

      case (TransputerConstants.OPR) => 
        stdout.printf("opr ")
        executeSecondaryInstruction()

      case (TransputerConstants.LDC) => 
        stdout.printf("ldc\n")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = registers.Oreg
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.LDL) => 
        stdout.printf("ldl\n")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = RIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), registers.Oreg)
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.STL) => 
        stdout.printf("stl\n")
        WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), registers.Oreg, registers.Areg)
        registers.Areg = registers.Breg
        registers.Breg = registers.Creg
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.LDLP) => 
        stdout.printf("ldlp\n")
        registers.Creg = registers.Breg
        registers.Breg = registers.Areg
        registers.Areg = AtWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), registers.Oreg)
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.ADC) => 
        stdout.printf("adc\n")
        overflowCheck(TransputerConstants.ADD, registers.Oreg, registers.Areg)
        registers.Areg = registers.Areg + registers.Oreg
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.EQC) => 
        stdout.printf("eqc\n")
        registers.Areg = if (registers.Areg == registers.Oreg) 1 else 0
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.J) => 
        stdout.printf("j\n")
        registers.Iptr = atByte(registers.Iptr + 1, registers.Oreg)
        registers.Oreg = 0

      case (TransputerConstants.CJ) => 
        stdout.printf("cj\n")
        if (registers.Areg == 0) {
          registers.Iptr = atByte(registers.Iptr + 1, registers.Oreg)
        } else {
          registers.Areg = registers.Breg
          registers.Breg = registers.Creg
          registers.Creg = 0
          registers.Iptr += 1
        }
        registers.Oreg = 0

      case (TransputerConstants.LDNL) => 
        stdout.printf("ldnl\n")
        registers.Areg = RIndexWord(registers.Areg, registers.Oreg)
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.STNL) => 
        stdout.printf("stnl\n")
        WIndexWord(registers.Areg, registers.Oreg, registers.Breg)
        registers.Areg = registers.Creg
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.LDNLP) => 
        stdout.printf("ldnlp\n")
        registers.Areg = AtWord(registers.Areg, registers.Oreg)
        registers.Oreg = 0
        registers.Iptr += 1

      case (TransputerConstants.CALL) => 
        stdout.printf("call\n")



        WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), -1, registers.Creg)
        WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), -2, registers.Breg)
        WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), -3, registers.Areg)
        WIndexWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), -4, registers.Iptr + 1)

        processToUpdate = debuggerState.processes.stream.filter((p) => p.status eq ProcessStatus.RUNNING).filter((p) => p.getCurrentWptr eq registers.Wptr).findFirst.get

        registers.Areg = registers.Iptr + 1
        registers.Wptr = AtWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), -4) | 
          TransputerHelpers.extractPriorityBit(registers.Wptr)
        registers.Iptr = atByte(registers.Iptr + 1, registers.Oreg)
        registers.Oreg = 0
        processToUpdate.updateWptr(registers.Wptr)

      case (TransputerConstants.AJW) => 
        stdout.printf("ajw\n")

        processToUpdate = debuggerState.processes.stream.filter((p) => p.status eq ProcessStatus.RUNNING).filter((p) => p.getCurrentWptr eq registers.Wptr).findFirst.get

        registers.Wptr = AtWord(TransputerHelpers.extractWorkspacePointer(registers.Wptr), registers.Oreg) | 
          TransputerHelpers.extractPriorityBit(registers.Wptr)
        registers.Oreg = 0
        registers.Iptr += 1
        processToUpdate.updateWptr(registers.Wptr)

      case _ => 
        System.err.printf("Instruction opcode '%02X' not implemented at Iptr '%08X'\n", opcode, registers.Iptr)
        System.exit(1)

    }
  }

  /**
   * Handle a request from an input channel to the processor.
   */
  private def handleInputChannelRequest(inputLink: InputLink, request: Int) {
    inputLink.toProcessor = TransputerConstants.NOIO
    if (request == TransputerConstants.RUNREQUEST) {
      var channelContent: Int = 0
      inputLink.fromProcessor = TransputerConstants.ACKRUN
      channelContent = inputLink.WptrToProcessor
      if (channelContent == TransputerConstants.NOTPROCESS_P) {
      } else {
        inputLink.Wptr = TransputerConstants.NOTPROCESS_P
        runProcess(channelContent)
      }
    } else if (request == TransputerConstants.READYREQUEST) {
      var channelContent: Int = 0
      var procPtr: Int = 0
      var status: Int = 0
      inputLink.fromProcessor = TransputerConstants.ACKREADY
      channelContent = inputLink.WptrToProcessor
      procPtr = TransputerHelpers.extractWorkspacePointer(channelContent)
      status = RIndexWord(procPtr, TransputerConstants.POINTER_S)
      if (status == TransputerConstants.ENABLING_P) {
        WIndexWord(procPtr, TransputerConstants.POINTER_S, TransputerConstants.READY_P)
      } else if (status == TransputerConstants.READY_P) {
      } else if (status == TransputerConstants.WAITING_P) {
        WIndexWord(procPtr, TransputerConstants.POINTER_S, TransputerConstants.READY_P)
        runProcess(channelContent)
      }
    }
  }

  /**
   * Handle a request from an output channel to the processor.
   */
  private def handleOutputChannelRequest(outputLink: OutputLink, request: Int) {
    outputLink.toProcessor = TransputerConstants.NOIO
    if (request == TransputerConstants.RUNREQUEST) {
      var channelContent: Int = 0
      outputLink.fromProcessor = TransputerConstants.ACKRUN
      channelContent = outputLink.WptrToProcessor
      if (channelContent == TransputerConstants.NOTPROCESS_P) {
      } else {
        outputLink.Wptr = TransputerConstants.NOTPROCESS_P
        runProcess(channelContent)
      }
    } else if (request == TransputerConstants.READYREQUEST) {
      var channelContent: Int = 0
      var procPtr: Int = 0
      var status: Int = 0
      outputLink.fromProcessor = TransputerConstants.ACKREADY
      channelContent = outputLink.WptrToProcessor
      procPtr = TransputerHelpers.extractWorkspacePointer(channelContent)
      status = RIndexWord(procPtr, TransputerConstants.POINTER_S)
      if (status == TransputerConstants.ENABLING_P) {
        WIndexWord(procPtr, TransputerConstants.POINTER_S, TransputerConstants.READY_P)
      } else if (status == TransputerConstants.READY_P) {
      } else if (status == TransputerConstants.WAITING_P) {
        WIndexWord(procPtr, TransputerConstants.POINTER_S, TransputerConstants.READY_P)
        runProcess(channelContent)
      }
    }
  }

  /**
   * Check to see if the input or output ports are transmitting or receiving data
   */
  private def checkChannels(): Boolean = {
    var i: Int = 0
    i = 0
    while (i < TransputerConstants.IN_PORTS) {
      if (inputLinks(i).toProcessor != TransputerConstants.NOIO) {
        handleInputChannelRequest(inputLinks(i), inputLinks(i).toProcessor)
        return true
      }
      i += 1
    }
    if (outputLink.toProcessor != TransputerConstants.NOIO) {
      handleOutputChannelRequest(outputLink, outputLink.toProcessor)
      return true
    }
    false
  }

  /**
   * Execute a single transputer instruction
   * @return true if the process is valid, false otherwise
   */
  def performStep(): Boolean = {
    val completed = sreg.gotoStartNewProcess || sreg.ioBit || sreg.moveBit || 
      sreg.timeIns || 
      sreg.timeDel
    if (sreg.gotoStartNewProcess) {
      stdout.printf("performStep => startNewProcess\n")
      startNewProcess()
      return true
    } else if (TEnabled(0) && 
      TransputerHelpers.extractPriorityBit(registers.Wptr) == 
      0 && 
      completed && 
      Later(ClockReg(0), TNextReg(0))) {
      stdout.printf("performStep => handleTimerRequest(0), PRIORITY(0)\n")
      handleTimerRequest(HIGH)
      return true
    } else if (completed && checkChannels()) {
      return true
    } else if (TEnabled(0) && 
      TransputerHelpers.extractPriorityBit(registers.Wptr) == 
      1 && 
      Later(ClockReg(0), TNextReg(0))) {
      stdout.printf("performStep => transputer_handle_timer_reg(0), PRIORITY(1)\n")
      handleTimerRequest(HIGH)
      return true
    } else if (TEnabled(1) && 
      TransputerHelpers.extractPriorityBit(registers.Wptr) == 
      1 && 
      completed && 
      Later(ClockReg(1), TNextReg(1))) {
      stdout.printf("performStep => transputer_handle_timer_reg(1), PRIORITY(1)\n")
      handleTimerRequest(LOW)
      return true
    }
    if (TransputerHelpers.extractWorkspacePointer(registers.Wptr) == 
      TransputerConstants.NOTPROCESS_P) {
      stdout.printf("WARNING: performStep() 'Wptr' == NOTPROCESS_P\n")
      return false
    }
    if (sreg.timeDel) {
      timerQueueDeleteMiddleStep()
    } else if (sreg.timeIns) {
      timerQueueInsertMiddleStep()
    } else if (sreg.moveBit) {
      blockMoveMiddleStep()
    } else {
      executePrimaryInstruction()
    }
    true
  }

  def incrementClock(loopCount: Long) {
    ClockReg(0) += 1
    if (loopCount % 4 == 0) {
      ClockReg(1) += 1
    }
  }

  def logState(index: Long, wr: PrintWriter) {
    wr.printf("%10X %08X %08X %08X %08X %08X %08X %01b %01b\n", index, registers.Areg, registers.Breg, 
      registers.Creg, registers.Oreg, registers.Iptr, registers.Wptr, sreg.errorFlag, sreg.haltOnErr)
  }

  def logSched(index: Long, wr: PrintWriter) {
    logState(index, wr)
    wr.printf("%08X %08X %08X %08X %08X %01b %01b %01b\n", FptrReg(0), BptrReg(0), FptrReg(1), BptrReg(1), 
      Ereg, sreg.gotoStartNewProcess, sreg.moveBit, sreg.ioBit)
  }

  def logTimer(index: Long, wr: PrintWriter) {
    logSched(index, wr)
    wr.printf("%08X %08X %08b %08b %01b %01b\n", TNextReg(0), TNextReg(1), TEnabled(0), TEnabled(1), 
      sreg.timeIns, sreg.timeDel)
  }
}
