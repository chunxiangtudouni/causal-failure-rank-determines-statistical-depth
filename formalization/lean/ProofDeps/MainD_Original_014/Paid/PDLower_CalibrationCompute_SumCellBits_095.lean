module

public import Paid.PDLower_CalibrationCompute_SumLeadBits_094
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_OperandPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem sumCell_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (row : Array ℚ) (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (inside : header.cursor<row.size) (fresh : before.register .fresh=.natural base)
    (index : before.register .index=.natural header.cursor) (safe : SafeBits before budget)
    (slot7Bits : 1+natBits (base+7)≤budget) (slot9Bits : 1+natBits (base+9)≤budget)
    (slot11Bits : 1+natBits (base+11)≤budget)
    (cellAddressBits : (Cell.natural (header.readBase+header.cursor)).bits≤budget)
    (addedBits : (Cell.rational (header.q+row.getD header.cursor 0)).bits≤budget)
    (oneBits : (Cell.natural 1).bits≤budget) (nextBits : (Cell.natural (header.cursor+1)).bits≤budget)
    (pcBits : natBits (before.pc+20)≤budget) :
    PrefixSafe input (basicBlock .sumCell).body before budget := by
  have read := represented.lookup (offset:=9) (value:=.natural header.readBase) rfl
  have sum := represented.lookup (offset:=11) (value:=.rational header.q) rfl
  have cursor := represented.lookup (offset:=7) (value:=.natural header.cursor) rfl
  let d := sumCellLeadResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)
  let e := storeSlotResult d base 11 .value
  have leadRun : linearExecute input sumCellLeadCode before=some d :=
    sumCellLead_execute input before base header.readBase header.cursor header.q (row.getD header.cursor 0)
      fresh index read.2 read.1 sum.2 sum.1 (rowAt.live _ inside) (rowAt.value _ inside)
  have leadSafe := sumCellLead_prefix_safe input before base header.readBase header.cursor budget
    header.q (row.getD header.cursor 0) safe fresh index read.2 read.1 sum.2 sum.1
    (rowAt.live _ inside) (rowAt.value _ inside) slot9Bits slot11Bits cellAddressBits addedBits
    ((PDROC.DataBits.natBits_mono (by omega : before.pc+9≤before.pc+20)).trans pcBits)
  have dFresh : d.register .fresh=.natural base := by simp [d,sumCellLeadResult,loadSlotResult,fresh]
  have storeRun : linearExecute input (storeSlot 11 .value) d=some e :=
    storeSlot_execute input d base 11 .value dFresh (by decide)
  have storeSafe := PrefixSafe.storeSlot input d base 11 budget .value (leadSafe.final leadRun) dFresh
    (by decide) slot11Bits (by simpa only [d,sumCellLeadResult,loadSlotResult,Nat.add_assoc] using
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+12≤before.pc+20)).trans pcBits))
  have eFresh : e.register .fresh=.natural base := by simp [e,storeSlotResult,dFresh]
  have eLive : base+7∈e.live := Finset.mem_insert_of_mem cursor.2
  have eCursor : e.heap (base+7)=.natural header.cursor := by
    simpa [e,d,storeSlotResult,sumCellLeadResult,loadSlotResult] using cursor.1
  have incrementSafe := increment_prefix_safe input e base 7 header.cursor budget (storeSafe.final storeRun)
    eFresh eLive eCursor slot7Bits oneBits nextBits
    (by simpa only [e,d,storeSlotResult,sumCellLeadResult,loadSlotResult,Nat.add_assoc] using pcBits)
  have tailSafe := PrefixSafe.append input (storeSlot 11 .value) (incrementSlot 7) d e budget
    storeRun storeSafe incrementSafe
  have all := PrefixSafe.append input sumCellLeadCode (storeSlot 11 .value++incrementSlot 7)
    before d budget leadRun leadSafe tailSafe
  simpa only [basicBlock,sumCellLeadCode,List.append_assoc] using all

/-- All twenty literal body prefixes and the actual jump of one sum
iteration retain caller B, on the same true fetched trace. -/
theorem sumCell_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ) (header : Header)
    (row : Array ℚ) (position : before.pc=labelAddress origin .sumCell)
    (represented : header.At before base) (rowAt : RowAt before header.readBase row)
    (inside : header.cursor<row.size) (fresh : before.register .fresh=.natural base)
    (index : before.register .index=.natural header.cursor) (safe : SafeBits before budget)
    (slot7Bits : 1+natBits (base+7)≤budget) (slot9Bits : 1+natBits (base+9)≤budget)
    (slot11Bits : 1+natBits (base+11)≤budget)
    (cellAddressBits : (Cell.natural (header.readBase+header.cursor)).bits≤budget)
    (addedBits : (Cell.rational (header.q+row.getD header.cursor 0)).bits≤budget)
    (oneBits : (Cell.natural 1).bits≤budget) (nextBits : (Cell.natural (header.cursor+1)).bits≤budget)
    (pcBits : natBits (before.pc+20)≤budget) (targetBits : natBits (labelAddress origin .sumGate)≤budget) :
    BitSegment origin input before
      {(sumCellResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)) with
        pc:=labelAddress origin .sumGate} 330 budget := by
  let middle := sumCellResult before base header.readBase header.cursor header.q (row.getD header.cursor 0)
  let after : State := {middle with pc:=labelAddress origin .sumGate}
  have body : linearExecute input (basicBlock .sumCell).body before=some middle :=
    sumCell_execute input before base header row represented rowAt inside fresh index
  have prefixes := sumCell_prefix_safe input before base budget header row represented rowAt inside fresh index safe
    slot7Bits slot9Bits slot11Bits cellAddressBits addedBits oneBits nextBits pcBits
  have control : (controlInstruction origin (basicBlock .sumCell).control).execute input middle=some after := rfl
  have last : SafeBits after budget := (prefixes.final body).withPC _ targetBits
  exact BitSegment.ofBlock origin .sumCell input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) last

end PDLower.CalibrationCompute
