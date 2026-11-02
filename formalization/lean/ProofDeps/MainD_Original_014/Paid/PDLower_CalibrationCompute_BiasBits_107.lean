module

public import Paid.PDLower_CalibrationCompute_Bias_023
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_ControlOperands_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem enterBiasLead_prefix_safe (input : List Cell) (before : State) (base budget : ℕ) (gamma : ℚ)
    (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (gammaLive : base+4∈before.live) (gammaValue : before.heap (base+4)=.rational gamma)
    (slotBits : 1+natBits (base+4)≤budget) (halfBits : (Cell.rational (1/2)).bits≤budget)
    (minusBits : (Cell.rational (1/2-gamma)).bits≤budget) (plusBits : (Cell.rational (1/2+gamma)).bits≤budget)
    (pcBits : natBits (before.pc+6)≤budget) : PrefixSafe input enterBiasPrefixCode before budget := by
  let a := loadSlotResult before base 4 .value
  let b := ({a with pc:=a.pc+1}).set .flag (.rational (1/2))
  let c := ({b with pc:=b.pc+1}).set .old (.rational (1/2-gamma))
  have pcSmall (offset : ℕ) (bounded : offset≤6) : natBits (before.pc+offset)≤budget :=
    (PDROC.DataBits.natBits_mono (Nat.add_le_add_left bounded before.pc)).trans pcBits
  have aRun : linearExecute input (loadSlot 4 .value) before=some a := loadSlot_execute input before base 4 .value fresh gammaLive
  have aSafe := PrefixSafe.loadSlot input before base 4 budget .value safe fresh gammaLive slotBits (pcSmall 3 (by decide))
  have bRun : linearExecute input [.constant .flag (.rational (1/2))] a=some b := rfl
  have bSafe := PrefixSafe.constant input a budget .flag (.rational (1/2)) (aSafe.final aRun) halfBits
    (by simpa only [a,loadSlotResult,Nat.add_assoc] using pcSmall 4 (by decide))
  have cRun : linearExecute input [.ratOp .subtract .old .flag .value] b=some c := by
    simp [linearExecute,Instruction.execute,Cell.rat?,RatOp.eval,c,b,a,loadSlotResult,State.set,gammaValue]
  have cSafe := PrefixSafe.ratOp input b budget .subtract .old .flag .value (1/2) gamma (1/2-gamma)
    (bSafe.final bRun) (by simp [b,State.set]) (by simp [b,a,State.set,loadSlotResult,gammaValue]) rfl minusBits
    (by simpa only [b,a,State.set,loadSlotResult,Nat.add_assoc] using pcSmall 5 (by decide))
  have lastSafe := PrefixSafe.ratOp input c budget .add .total .flag .value (1/2) gamma (1/2+gamma)
    (cSafe.final cRun) (by simp [c,b,State.set]) (by simp [c,b,a,State.set,loadSlotResult,gammaValue]) rfl plusBits
    (by simpa only [c,b,a,State.set,loadSlotResult,Nat.add_assoc] using pcBits)
  have tailC := PrefixSafe.append input [.ratOp .subtract .old .flag .value] [.ratOp .add .total .flag .value]
    b c budget cRun cSafe lastSafe
  have tailB := PrefixSafe.append input [.constant .flag (.rational (1/2))]
    ([.ratOp .subtract .old .flag .value]++[.ratOp .add .total .flag .value]) a b budget bRun bSafe tailC
  have all := PrefixSafe.append input (loadSlot 4 .value) ([.constant .flag (.rational (1/2))]++
    ([.ratOp .subtract .old .flag .value]++[.ratOp .add .total .flag .value])) before a budget aRun aSafe tailB
  simpa only [enterBiasPrefixCode,List.cons_append,List.nil_append] using all

theorem enterBias_prefix_safe (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ)
    (bounds : ControlBudget P origin base budget) (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (gammaLive : base+4∈before.live) (gammaValue : before.heap (base+4)=.rational P.certificate.gamma)
    (halfBits : (Cell.rational (1/2)).bits≤budget)
    (minusBits : (Cell.rational (1/2-P.certificate.gamma)).bits≤budget)
    (plusBits : (Cell.rational (1/2+P.certificate.gamma)).bits≤budget)
    (position : before.pc=labelAddress origin .enterBias) : PrefixSafe input (basicBlock .enterBias).body before budget := by
  let a := enterBiasComputed before base P.certificate.gamma
  let b := storeSlotResult a base 12 .old
  let c := storeSlotResult b base 13 .total
  let d := constantSlotResult c base 6 (.natural 0)
  let e := constantSlotResult d base 7 (.natural 0)
  let f := constantSlotResult e base 8 (.natural 0)
  let g := constantSlotResult f base 11 (.rational 0)
  have pcSmall (offset : ℕ) (bounded : offset≤32) : natBits (before.pc+offset)≤budget :=
    ControlBudget.pc_prefix P origin base budget bounds before .enterBias offset position bounded
  have zeroNat := ControlBudget.literal P origin base budget 0 bounds (by decide)
  have zeroRat : (Cell.rational 0).bits≤budget := by
    have literal : (Cell.rational 0).bits=4 := by decide
    rw [literal]
    exact bounds.small
  have aRun : linearExecute input enterBiasPrefixCode before=some a := enterBiasPrefix_execute input before base _ fresh gammaLive gammaValue
  have aSafe := enterBiasLead_prefix_safe input before base budget P.certificate.gamma safe fresh gammaLive gammaValue
    (ControlBudget.slot P origin base budget 4 bounds (by decide)) halfBits minusBits plusBits (pcSmall 6 (by decide))
  have aFresh : a.register .fresh=.natural base := (enterBiasComputed_fresh before base _).trans fresh
  have bRun : linearExecute input (storeSlot 12 .old) a=some b := storeSlot_execute input a base 12 .old aFresh (by decide)
  have bSafe := PrefixSafe.storeSlot input a base 12 budget .old (aSafe.final aRun) aFresh (by decide)
    (ControlBudget.slot P origin base budget 12 bounds (by decide))
    (by simpa only [a,enterBiasComputed,loadSlotResult,Nat.add_assoc] using pcSmall 9 (by decide))
  have bFresh : b.register .fresh=.natural base := by simp [b,storeSlotResult,aFresh]
  have cRun : linearExecute input (storeSlot 13 .total) b=some c := storeSlot_execute input b base 13 .total bFresh (by decide)
  have cSafe := PrefixSafe.storeSlot input b base 13 budget .total (bSafe.final bRun) bFresh (by decide)
    (ControlBudget.slot P origin base budget 13 bounds (by decide))
    (by simpa only [b,a,storeSlotResult,enterBiasComputed,loadSlotResult,Nat.add_assoc] using pcSmall 12 (by decide))
  have cFresh : c.register .fresh=.natural base := by simp [c,storeSlotResult,bFresh]
  have dRun : linearExecute input (constantSlot 6 (.natural 0)) c=some d := constantSlot_execute input c base 6 (.natural 0) cFresh
  have dSafe := constantSlot_sameBudget input c base 6 budget (.natural 0) (cSafe.final cRun) cFresh zeroNat
    (ControlBudget.slot P origin base budget 6 bounds (by decide))
    (by simpa only [c,b,a,storeSlotResult,enterBiasComputed,loadSlotResult,Nat.add_assoc] using pcSmall 16 (by decide))
  have dFresh : d.register .fresh=.natural base := (constantSlot_fresh c base 6 (.natural 0)).trans cFresh
  have eRun : linearExecute input (constantSlot 7 (.natural 0)) d=some e := constantSlot_execute input d base 7 (.natural 0) dFresh
  have eSafe := constantSlot_sameBudget input d base 7 budget (.natural 0) (dSafe.final dRun) dFresh zeroNat
    (ControlBudget.slot P origin base budget 7 bounds (by decide))
    (by simpa only [d,c,b,a,constantSlotResult,storeSlotResult,State.set,enterBiasComputed,loadSlotResult,Nat.add_assoc] using pcSmall 20 (by decide))
  have eFresh : e.register .fresh=.natural base := (constantSlot_fresh d base 7 (.natural 0)).trans dFresh
  have fRun : linearExecute input (constantSlot 8 (.natural 0)) e=some f := constantSlot_execute input e base 8 (.natural 0) eFresh
  have fSafe := constantSlot_sameBudget input e base 8 budget (.natural 0) (eSafe.final eRun) eFresh zeroNat
    (ControlBudget.slot P origin base budget 8 bounds (by decide))
    (by simpa only [e,d,c,b,a,constantSlotResult,storeSlotResult,State.set,enterBiasComputed,loadSlotResult,Nat.add_assoc] using pcSmall 24 (by decide))
  have fFresh : f.register .fresh=.natural base := (constantSlot_fresh e base 8 (.natural 0)).trans eFresh
  have gRun : linearExecute input (constantSlot 11 (.rational 0)) f=some g := constantSlot_execute input f base 11 (.rational 0) fFresh
  have gSafe := constantSlot_sameBudget input f base 11 budget (.rational 0) (fSafe.final fRun) fFresh zeroRat
    (ControlBudget.slot P origin base budget 11 bounds (by decide))
    (by simpa only [f,e,d,c,b,a,constantSlotResult,storeSlotResult,State.set,enterBiasComputed,loadSlotResult,Nat.add_assoc] using pcSmall 28 (by decide))
  have gFresh : g.register .fresh=.natural base := (constantSlot_fresh f base 11 (.rational 0)).trans fFresh
  have lastSafe := constantSlot_sameBudget input g base 14 budget (.natural 0) (gSafe.final gRun) gFresh zeroNat
    (ControlBudget.slot P origin base budget 14 bounds (by decide))
    (by simpa only [g,f,e,d,c,b,a,constantSlotResult,storeSlotResult,State.set,enterBiasComputed,loadSlotResult,Nat.add_assoc] using pcSmall 32 (by decide))
  have tailG := PrefixSafe.append input (constantSlot 11 (.rational 0)) (constantSlot 14 (.natural 0)) f g budget gRun gSafe lastSafe
  have tailF := PrefixSafe.append input (constantSlot 8 (.natural 0))
    (constantSlot 11 (.rational 0)++constantSlot 14 (.natural 0)) e f budget fRun fSafe tailG
  have tailE := PrefixSafe.append input (constantSlot 7 (.natural 0))
    (constantSlot 8 (.natural 0)++(constantSlot 11 (.rational 0)++constantSlot 14 (.natural 0))) d e budget eRun eSafe tailF
  have tailD := PrefixSafe.append input (constantSlot 6 (.natural 0)) (constantSlot 7 (.natural 0)++
    (constantSlot 8 (.natural 0)++(constantSlot 11 (.rational 0)++constantSlot 14 (.natural 0)))) c d budget dRun dSafe tailE
  have tailC := PrefixSafe.append input (storeSlot 13 .total) (constantSlot 6 (.natural 0)++(constantSlot 7 (.natural 0)++
    (constantSlot 8 (.natural 0)++(constantSlot 11 (.rational 0)++constantSlot 14 (.natural 0))))) b c budget cRun cSafe tailD
  have tailB := PrefixSafe.append input (storeSlot 12 .old) (storeSlot 13 .total++(constantSlot 6 (.natural 0)++
    (constantSlot 7 (.natural 0)++(constantSlot 8 (.natural 0)++(constantSlot 11 (.rational 0)++constantSlot 14 (.natural 0)))))) a b budget bRun bSafe tailC
  have all := PrefixSafe.append input enterBiasPrefixCode (storeSlot 12 .old++(storeSlot 13 .total++
    (constantSlot 6 (.natural 0)++(constantSlot 7 (.natural 0)++(constantSlot 8 (.natural 0)++
      (constantSlot 11 (.rational 0)++constantSlot 14 (.natural 0))))))) before a budget aRun aSafe tailB
  simpa only [basicBlock,enterBiasPrefixCode,List.append_assoc] using all

theorem enterBias_bitSegment (P : Parameters) (origin : ℕ) (input : List Cell) (before : State) (base budget : ℕ)
    (bounds : ControlBudget P origin base budget) (safe : SafeBits before budget) (fresh : before.register .fresh=.natural base)
    (gammaLive : base+4∈before.live) (gammaValue : before.heap (base+4)=.rational P.certificate.gamma)
    (halfBits : (Cell.rational (1/2)).bits≤budget)
    (minusBits : (Cell.rational (1/2-P.certificate.gamma)).bits≤budget)
    (plusBits : (Cell.rational (1/2+P.certificate.gamma)).bits≤budget)
    (position : before.pc=labelAddress origin .enterBias) :
    BitSegment origin input before {(enterBiasResult before base P.certificate.gamma) with pc:=labelAddress origin .levelGate} 510 budget := by
  let middle := enterBiasResult before base P.certificate.gamma
  let after : State := {middle with pc:=labelAddress origin .levelGate}
  have body : linearExecute input (basicBlock .enterBias).body before=some middle := enterBias_execute input before base _ fresh gammaLive gammaValue
  have prefixes := enterBias_prefix_safe P origin input before base budget bounds safe fresh gammaLive gammaValue halfBits minusBits plusBits position
  have control : (controlInstruction origin (basicBlock .enterBias).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .enterBias input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed)
    ((prefixes.final body).withPC _ (ControlBudget.pc_target P origin base budget bounds .levelGate))

end PDLower.CalibrationCompute
