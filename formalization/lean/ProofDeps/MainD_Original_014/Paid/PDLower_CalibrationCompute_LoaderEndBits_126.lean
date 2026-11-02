module

public import Paid.PDLower_CalibrationCompute_StandaloneBitSegment_120
public import Paid.PDLower_CalibrationCompute_LoaderBudget_125
public import Paid.PDLower_CalibrationCompute_BootstrapEnd_068

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDMenu.ComputeFrame
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem bootstrapEnd_prefix_safe (P : Parameters) (input : List Cell) (before : State) (budget : ℕ)
    (bounds : LoaderOperandBounds P budget) (safe : SafeBits before budget) (position : before.pc=mainStart+20)
    (total : before.register .total=.natural P.certificate.M)
    (returnBits : (Cell.natural (mainStart+27)).bits≤budget) :
    PrefixSafe input bootstrapEndCode before budget := by
  let a := ({before with pc:=before.pc+1}).set .old (.natural 2)
  let b := ({a with pc:=a.pc+1}).set .fresh (.natural (P.certificate.M*2))
  let c := ({b with pc:=b.pc+1}).set .old (.natural 3)
  let d := ({c with pc:=c.pc+1}).set .fresh (.natural (rowWidth P.certificate.M))
  let e := ({d with pc:=d.pc+1}).set .address (.natural 0)
  let f := ({e with pc:=e.pc+1}).set .old (.natural (mainStart+27))
  have pcSmall (offset : ℕ) (bounded : offset≤6) : natBits (before.pc+offset)≤budget := bounds.pc _ (by rw [position];omega)
  have aSafe : SafeBits a budget := (safe.withPC _ (pcSmall 1 (by decide))).set .old _
    (LoaderOperandBounds.literal P budget 2 bounds (by decide))
  have bRun : (.natOp .multiply .fresh .total .old : Instruction).execute input a=some b := by
    simp [Instruction.execute,Cell.nat?,NatOp.eval,b,a,State.set,total]
  have bSafe : SafeBits b budget := (aSafe.withPC _ (by simpa only [a,State.set,Nat.add_assoc] using pcSmall 2 (by decide))).set .fresh _
    (bounds.natural _ (by unfold rowWidth;omega))
  have cSafe : SafeBits c budget := (bSafe.withPC _ (by simpa only [b,a,State.set,Nat.add_assoc] using pcSmall 3 (by decide))).set .old _
    (LoaderOperandBounds.literal P budget 3 bounds (by decide))
  have dRun : (.natOp .add .fresh .fresh .old : Instruction).execute input c=some d := by
    simp [Instruction.execute,Cell.nat?,NatOp.eval,d,c,b,State.set,rowWidth,Nat.mul_comm]
  have dSafe : SafeBits d budget := (cSafe.withPC _ (by simpa only [c,b,a,State.set,Nat.add_assoc] using pcSmall 4 (by decide))).set .fresh _
    (bounds.natural _ (by omega))
  have eSafe : SafeBits e budget := (dSafe.withPC _ (by simpa only [d,c,b,a,State.set,Nat.add_assoc] using pcSmall 5 (by decide))).set .address _
    (LoaderOperandBounds.literal P budget 0 bounds (by decide))
  have fSafe : SafeBits f budget := (eSafe.withPC _ (by simpa only [e,d,c,b,a,State.set,Nat.add_assoc] using pcSmall 6 (by decide))).set .old _ returnBits
  unfold bootstrapEndCode
  apply PrefixSafe.cons _ _ _ before a budget rfl safe
  apply PrefixSafe.cons _ _ _ a b budget bRun aSafe
  apply PrefixSafe.cons _ _ _ b c budget rfl bSafe
  apply PrefixSafe.cons _ _ _ c d budget dRun cSafe
  apply PrefixSafe.cons _ _ _ d e budget rfl dSafe
  apply PrefixSafe.cons _ _ _ e f budget rfl eSafe
  exact PrefixSafe.nil _ f budget fSafe

theorem bootstrapEnd_bits (P : Parameters) (input : List Cell) (before : State) (budget : ℕ)
    (bounds : LoaderOperandBounds P budget) (safe : SafeBits before budget) (position : before.pc=mainStart+20)
    (total : before.register .total=.natural P.certificate.M)
    (returnBits : (Cell.natural (mainStart+27)).bits≤budget) :
    StandaloneBitSegment input before (bootstrapEndResult before P.certificate.M) 120 budget := by
  let middle := bootstrapEndBodyResult before P.certificate.M
  let after := bootstrapEndResult before P.certificate.M
  have fetch : FetchesCode calibrate before.pc bootstrapEndCode := by
    intro offset inside
    rw [position]
    exact bootstrapEnd_fetch offset inside
  have executed := bootstrapEnd_execute input before P.certificate.M total
  have prefixes := bootstrapEnd_prefix_safe P input before budget bounds safe position total returnBits
  have control : step calibrate input middle=some after := by
    have pc : middle.pc=mainStart+26 := by dsimp [middle,bootstrapEndBodyResult];omega
    simp only [step,pc,calibrate_call_fetch,Instruction.execute]
    rfl
  exact standalone_bits_linearControl input bootstrapEndCode before middle after budget bootstrapEnd_straight fetch executed prefixes control
    ((prefixes.final executed).withPC _ (bounds.pc _ (by omega)))

end PDLower.CalibrationCompute
