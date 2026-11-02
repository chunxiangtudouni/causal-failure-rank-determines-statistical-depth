module

public import Paid.PDLower_CalibrationCompute_Enter_014
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Actual sixteen-opcode argument save, including preserving the
original endpoint pointer before the address scratch is overwritten. -/
theorem prologue_prefix_safe (input : List Cell) (before : State) (base budget : ℕ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (addresses : ∀ offset≤4,1+natBits (base+offset)≤budget)
    (pcBits : natBits (before.pc+16)≤budget) : PrefixSafe input prologue before budget := by
  let moved := ({before with pc:=before.pc+1}).set .flag (before.register .address)
  let a := storeSlotResult moved base 0 .old
  let b := storeSlotResult a base 1 .flag
  let c := storeSlotResult b base 2 .total
  let d := storeSlotResult c base 3 .index
  have pcSmall (offset : ℕ) (bounded : offset≤16) : natBits (before.pc+offset)≤budget :=
    (PDROC.DataBits.natBits_mono (Nat.add_le_add_left bounded before.pc)).trans pcBits
  have moveRun : linearExecute input [.move .flag .address] before=some moved := rfl
  have moveSafe := PrefixSafe.move input before budget .flag .address safe (pcSmall 1 (by decide))
  have movedFresh : moved.register .fresh=.natural base := by simp [moved,State.set,fresh]
  have aRun : linearExecute input (storeSlot 0 .old) moved=some a :=
    storeSlot_execute input moved base 0 .old movedFresh (by decide)
  have aSafe := PrefixSafe.storeSlot input moved base 0 budget .old (moveSafe.final moveRun) movedFresh (by decide)
    (addresses 0 (by decide)) (by simpa only [moved,State.set,Nat.add_assoc] using pcSmall 4 (by decide))
  have aFresh : a.register .fresh=.natural base := by simp [a,storeSlotResult,movedFresh]
  have bRun : linearExecute input (storeSlot 1 .flag) a=some b := storeSlot_execute input a base 1 .flag aFresh (by decide)
  have bSafe := PrefixSafe.storeSlot input a base 1 budget .flag (aSafe.final aRun) aFresh (by decide)
    (addresses 1 (by decide)) (by simpa only [a,moved,storeSlotResult,State.set,Nat.add_assoc] using pcSmall 7 (by decide))
  have bFresh : b.register .fresh=.natural base := by simp [b,storeSlotResult,aFresh]
  have cRun : linearExecute input (storeSlot 2 .total) b=some c := storeSlot_execute input b base 2 .total bFresh (by decide)
  have cSafe := PrefixSafe.storeSlot input b base 2 budget .total (bSafe.final bRun) bFresh (by decide)
    (addresses 2 (by decide)) (by simpa only [b,a,moved,storeSlotResult,State.set,Nat.add_assoc] using pcSmall 10 (by decide))
  have cFresh : c.register .fresh=.natural base := by simp [c,storeSlotResult,bFresh]
  have dRun : linearExecute input (storeSlot 3 .index) c=some d := storeSlot_execute input c base 3 .index cFresh (by decide)
  have dSafe := PrefixSafe.storeSlot input c base 3 budget .index (cSafe.final cRun) cFresh (by decide)
    (addresses 3 (by decide)) (by simpa only [c,b,a,moved,storeSlotResult,State.set,Nat.add_assoc] using pcSmall 13 (by decide))
  have dFresh : d.register .fresh=.natural base := by simp [d,storeSlotResult,cFresh]
  have lastSafe := PrefixSafe.storeSlot input d base 4 budget .value (dSafe.final dRun) dFresh (by decide)
    (addresses 4 (by decide)) (by simpa only [d,c,b,a,moved,storeSlotResult,State.set,Nat.add_assoc] using pcBits)
  have tailD := PrefixSafe.append input (storeSlot 3 .index) (storeSlot 4 .value) c d budget dRun dSafe lastSafe
  have tailC := PrefixSafe.append input (storeSlot 2 .total) (storeSlot 3 .index++storeSlot 4 .value) b c budget cRun cSafe tailD
  have tailB := PrefixSafe.append input (storeSlot 1 .flag) (storeSlot 2 .total++(storeSlot 3 .index++storeSlot 4 .value))
    a b budget bRun bSafe tailC
  have tailA := PrefixSafe.append input (storeSlot 0 .old)
    (storeSlot 1 .flag++(storeSlot 2 .total++(storeSlot 3 .index++storeSlot 4 .value))) moved a budget aRun aSafe tailB
  have all := PrefixSafe.append input [.move .flag .address]
    (storeSlot 0 .old++(storeSlot 1 .flag++(storeSlot 2 .total++(storeSlot 3 .index++storeSlot 4 .value))))
    before moved budget moveRun moveSafe tailA
  simpa only [prologue,List.append_assoc] using all

theorem enter_bitSegment (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ)
    (position : before.pc=labelAddress origin .enter)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (addresses : ∀ offset≤4,1+natBits (base+offset)≤budget)
    (pcBits : natBits (before.pc+16)≤budget) (targetBits : natBits (labelAddress origin .enterBases)≤budget) :
    BitSegment origin input before {(prologueResult before base) with pc:=labelAddress origin .enterBases} 270 budget := by
  let middle := prologueResult before base
  let after : State := {middle with pc:=labelAddress origin .enterBases}
  have body : linearExecute input (basicBlock .enter).body before=some middle := prologue_execute input before base fresh
  have prefixes := prologue_prefix_safe input before base budget safe fresh addresses pcBits
  have control : (controlInstruction origin (basicBlock .enter).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .enter input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) ((prefixes.final body).withPC _ targetBits)

end PDLower.CalibrationCompute
