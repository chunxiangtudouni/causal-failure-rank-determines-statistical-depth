module

public import Paid.PDLower_CalibrationCompute_StandaloneBitSegment_120
public import Paid.PDLower_CalibrationCompute_LoaderBudget_125

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDMenu.ComputeFrame
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem bootstrapStart_prefix_safe (P : Parameters) (before : State) (budget : ℕ)
    (bounds : LoaderOperandBounds P budget) (safe : SafeBits before budget) (position : before.pc=mainStart) :
    PrefixSafe (calibrationInput P) bootstrapStartCode before budget := by
  let a := ({before with pc:=before.pc+1}).set .address (.natural 0)
  let b := ({a with pc:=a.pc+1}).set .total (.natural P.certificate.M)
  let c := ({b with pc:=b.pc+1}).set .address (.natural 1)
  let d := ({c with pc:=c.pc+1}).set .index (.natural P.certificate.Q)
  let e := ({d with pc:=d.pc+1}).set .address (.natural 2)
  let f := ({e with pc:=e.pc+1}).set .value (.rational P.certificate.gamma)
  let g := ({f with pc:=f.pc+1}).set .old (.natural 2)
  let h := ({g with pc:=g.pc+1}).set .flag (.natural (P.certificate.M*2))
  let i := ({h with pc:=h.pc+1}).set .old (.natural 3)
  let j := ({i with pc:=i.pc+1}).set .flag (.natural (rowWidth P.certificate.M))
  let k := ({j with pc:=j.pc+1}).set .address (.natural 0)
  let l := ({k with pc:=k.pc+1}).set .old (.natural 3)
  have pcSmall (offset : ℕ) (bounded : offset≤12) : natBits (before.pc+offset)≤budget :=
    bounds.pc _ (by rw [position];omega)
  have zeroBits := LoaderOperandBounds.literal P budget 0 bounds (by decide)
  have oneBits := LoaderOperandBounds.literal P budget 1 bounds (by decide)
  have twoBits := LoaderOperandBounds.literal P budget 2 bounds (by decide)
  have threeBits := LoaderOperandBounds.literal P budget 3 bounds (by decide)
  have mBits := bounds.input (.natural P.certificate.M) (by simp [calibrationInput])
  have qBits := bounds.input (.natural P.certificate.Q) (by simp [calibrationInput])
  have gammaBits := bounds.input (.rational P.certificate.gamma) (by simp [calibrationInput])
  have aSafe : SafeBits a budget := (safe.withPC _ (pcSmall 1 (by decide))).set .address _ zeroBits
  have bRun : (.loadInput .total .address : Instruction).execute (calibrationInput P) a=some b := by
    simp [Instruction.execute,Cell.nat?,a,b,State.set,calibrationInput]
  have bSafe : SafeBits b budget := loadInput_execute_safe (calibrationInput P) a b .total .address 0 budget _ aSafe
    (by simp [a,State.set]) (by simp [calibrationInput]) mBits
    (by simpa only [a,State.set,Nat.add_assoc] using pcSmall 2 (by decide)) bRun
  have cSafe : SafeBits c budget := (bSafe.withPC _ (by simpa only [b,a,State.set,Nat.add_assoc] using pcSmall 3 (by decide))).set .address _ oneBits
  have dRun : (.loadInput .index .address : Instruction).execute (calibrationInput P) c=some d := by
    simp [Instruction.execute,Cell.nat?,c,d,State.set,calibrationInput]
  have dSafe : SafeBits d budget := loadInput_execute_safe (calibrationInput P) c d .index .address 1 budget _ cSafe
    (by simp [c,State.set]) (by simp [calibrationInput]) qBits
    (by simpa only [c,b,a,State.set,Nat.add_assoc] using pcSmall 4 (by decide)) dRun
  have eSafe : SafeBits e budget := (dSafe.withPC _ (by simpa only [d,c,b,a,State.set,Nat.add_assoc] using pcSmall 5 (by decide))).set .address _ twoBits
  have fRun : (.loadInput .value .address : Instruction).execute (calibrationInput P) e=some f := by
    simp [Instruction.execute,Cell.nat?,e,f,State.set,calibrationInput]
  have fSafe : SafeBits f budget := loadInput_execute_safe (calibrationInput P) e f .value .address 2 budget _ eSafe
    (by simp [e,State.set]) (by simp [calibrationInput]) gammaBits
    (by simpa only [e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 6 (by decide)) fRun
  have gSafe : SafeBits g budget := (fSafe.withPC _ (by simpa only [f,e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 7 (by decide))).set .old _ twoBits
  have hRun : (.natOp .multiply .flag .total .old : Instruction).execute (calibrationInput P) g=some h := by
    simp [Instruction.execute,Cell.nat?,NatOp.eval,h,g,f,e,d,c,b,State.set]
  have hSafe : SafeBits h budget := (gSafe.withPC _ (by simpa only [g,f,e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 8 (by decide))).set .flag _
    (bounds.natural _ (by unfold rowWidth;omega))
  have iSafe : SafeBits i budget := (hSafe.withPC _ (by simpa only [h,g,f,e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 9 (by decide))).set .old _ threeBits
  have jRun : (.natOp .add .flag .flag .old : Instruction).execute (calibrationInput P) i=some j := by
    simp [Instruction.execute,Cell.nat?,NatOp.eval,j,i,h,State.set,rowWidth,Nat.mul_comm]
  have jSafe : SafeBits j budget := (iSafe.withPC _ (by simpa only [i,h,g,f,e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 10 (by decide))).set .flag _
    (bounds.natural _ (by omega))
  have kSafe : SafeBits k budget := (jSafe.withPC _ (by simpa only [j,i,h,g,f,e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 11 (by decide))).set .address _ zeroBits
  have lSafe : SafeBits l budget := (kSafe.withPC _ (by simpa only [k,j,i,h,g,f,e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 12 (by decide))).set .old _ threeBits
  unfold bootstrapStartCode
  apply PrefixSafe.cons _ _ _ before a budget rfl safe
  apply PrefixSafe.cons _ _ _ a b budget bRun aSafe
  apply PrefixSafe.cons _ _ _ b c budget rfl bSafe
  apply PrefixSafe.cons _ _ _ c d budget dRun cSafe
  apply PrefixSafe.cons _ _ _ d e budget rfl dSafe
  apply PrefixSafe.cons _ _ _ e f budget fRun eSafe
  apply PrefixSafe.cons _ _ _ f g budget rfl fSafe
  apply PrefixSafe.cons _ _ _ g h budget hRun gSafe
  apply PrefixSafe.cons _ _ _ h i budget rfl hSafe
  apply PrefixSafe.cons _ _ _ i j budget jRun iSafe
  apply PrefixSafe.cons _ _ _ j k budget rfl jSafe
  apply PrefixSafe.cons _ _ _ k l budget rfl kSafe
  exact PrefixSafe.nil _ l budget lSafe

theorem bootstrapStart_bits (P : Parameters) (before : State) (budget : ℕ)
    (bounds : LoaderOperandBounds P budget) (safe : SafeBits before budget) (position : before.pc=mainStart) :
    StandaloneBitSegment (calibrationInput P) before (bootstrapStartResult before P) 195 budget := by
  have fetch : FetchesCode calibrate before.pc bootstrapStartCode := by
    intro offset inside
    rw [position]
    exact bootstrapStart_fetch offset inside
  exact standalone_bits_linear (calibrationInput P) bootstrapStartCode before (bootstrapStartResult before P) budget
    bootstrapStart_straight fetch (bootstrapStart_execute P before) (bootstrapStart_prefix_safe P before budget bounds safe position)

end PDLower.CalibrationCompute
