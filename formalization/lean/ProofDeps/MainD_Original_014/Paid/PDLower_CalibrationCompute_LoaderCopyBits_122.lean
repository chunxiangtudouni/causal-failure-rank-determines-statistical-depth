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

theorem bootstrapCopy_prefix_safe (P : Parameters) (before : State) (source destination remaining budget : ℕ) (value : Cell)
    (bounds : LoaderOperandBounds P budget) (safe : SafeBits before budget) (position : before.pc=mainStart+13)
    (old : before.register .old=.natural source) (address : before.register .address=.natural destination)
    (flag : before.register .flag=.natural remaining) (data : (calibrationInput P)[source]?=some value)
    (sourceEnd : source+1≤rowWidth P.certificate.M+3) (destinationEnd : destination+1≤rowWidth P.certificate.M+3)
    (remainingBound : remaining≤rowWidth P.certificate.M+3) :
    PrefixSafe (calibrationInput P) bootstrapCopyBody before budget := by
  let a := ({before with pc:=before.pc+1}).set .fresh value
  let b := writeCell a destination value
  let c := ({b with pc:=b.pc+1}).set .fresh (.natural 1)
  let d := ({c with pc:=c.pc+1}).set .old (.natural (source+1))
  let e := ({d with pc:=d.pc+1}).set .address (.natural (destination+1))
  let f := ({e with pc:=e.pc+1}).set .flag (.natural (remaining-1))
  have pcSmall (offset : ℕ) (bounded : offset≤6) : natBits (before.pc+offset)≤budget :=
    bounds.pc _ (by rw [position];omega)
  have aRun : (.loadInput .fresh .old : Instruction).execute (calibrationInput P) before=some a := by
    simp [Instruction.execute,Cell.nat?,old,data,a]
  have aSafe := loadInput_execute_safe (calibrationInput P) before a .fresh .old source budget value safe old data
    (bounds.input value (List.mem_of_getElem? data)) (pcSmall 1 (by decide)) aRun
  have bRun : linearExecute (calibrationInput P) [.store .address .fresh] a=some b := by
    simp [linearExecute,Instruction.execute,Cell.nat?,b,writeCell,a,State.set,address]
  have storeSafe := PrefixSafe.store (calibrationInput P) a budget .address .fresh destination aSafe
    (by simp [a,State.set,address]) (by simpa only [a,State.set,Nat.add_assoc] using pcSmall 2 (by decide))
  have bSafe := storeSafe.final bRun
  have cSafe : SafeBits c budget := (bSafe.withPC _ (by simpa only [b,a,writeCell,State.set,Nat.add_assoc] using pcSmall 3 (by decide))).set .fresh _
    (LoaderOperandBounds.literal P budget 1 bounds (by decide))
  have dRun : (.natOp .add .old .old .fresh : Instruction).execute (calibrationInput P) c=some d := by
    simp [Instruction.execute,Cell.nat?,NatOp.eval,d,c,b,a,writeCell,State.set,old]
  have dSafe : SafeBits d budget := (cSafe.withPC _ (by simpa only [c,b,a,writeCell,State.set,Nat.add_assoc] using pcSmall 4 (by decide))).set .old _
    (bounds.natural _ sourceEnd)
  have eRun : (.natOp .add .address .address .fresh : Instruction).execute (calibrationInput P) d=some e := by
    simp [Instruction.execute,Cell.nat?,NatOp.eval,e,d,c,b,a,writeCell,State.set,address]
  have eSafe : SafeBits e budget := (dSafe.withPC _ (by simpa only [d,c,b,a,writeCell,State.set,Nat.add_assoc] using pcSmall 5 (by decide))).set .address _
    (bounds.natural _ destinationEnd)
  have fRun : (.natOp .subtract .flag .flag .fresh : Instruction).execute (calibrationInput P) e=some f := by
    simp [Instruction.execute,Cell.nat?,NatOp.eval,f,e,d,c,b,a,writeCell,State.set,flag]
  have fSafe : SafeBits f budget := (eSafe.withPC _ (by simpa only [e,d,c,b,a,writeCell,State.set,Nat.add_assoc] using pcSmall 6 (by decide))).set .flag _
    (bounds.natural _ (by omega))
  have bExecuted : (.store .address .fresh : Instruction).execute (calibrationInput P) a=some b := by
    simp [Instruction.execute,Cell.nat?,b,writeCell,a,State.set,address]
  unfold bootstrapCopyBody
  apply PrefixSafe.cons _ _ _ before a budget aRun safe
  apply PrefixSafe.cons _ _ _ a b budget bExecuted aSafe
  apply PrefixSafe.cons _ _ _ b c budget rfl bSafe
  apply PrefixSafe.cons _ _ _ c d budget dRun cSafe
  apply PrefixSafe.cons _ _ _ d e budget eRun dSafe
  apply PrefixSafe.cons _ _ _ e f budget fRun eSafe
  exact PrefixSafe.nil _ f budget fSafe

theorem bootstrapCopy_bits (P : Parameters) (before : State) (source destination remaining budget : ℕ) (value : Cell)
    (bounds : LoaderOperandBounds P budget) (safe : SafeBits before budget) (position : before.pc=mainStart+13)
    (old : before.register .old=.natural source) (address : before.register .address=.natural destination)
    (flag : before.register .flag=.natural remaining) (data : (calibrationInput P)[source]?=some value)
    (sourceEnd : source+1≤rowWidth P.certificate.M+3) (destinationEnd : destination+1≤rowWidth P.certificate.M+3)
    (remainingBound : remaining≤rowWidth P.certificate.M+3) :
    StandaloneBitSegment (calibrationInput P) before
      {bootstrapCopyResult before source destination remaining value with pc:=mainStart+12} 120 budget := by
  let middle := bootstrapCopyResult before source destination remaining value
  let after : State := {middle with pc:=mainStart+12}
  have fetch : FetchesCode calibrate before.pc bootstrapCopyBody := by
    intro offset inside
    rw [position]
    exact calibrate_bootstrapCopy_fetch offset inside
  have executed := bootstrapCopy_execute (calibrationInput P) before source destination remaining value old address flag data
  have prefixes := bootstrapCopy_prefix_safe P before source destination remaining budget value bounds safe position old address flag data
    sourceEnd destinationEnd remainingBound
  have control : step calibrate (calibrationInput P) middle=some after := by
    have pc : middle.pc=mainStart+19 := by dsimp [middle,bootstrapCopyResult];omega
    have fetched : calibrate[middle.pc]?=some (.jump (mainStart+12)) := by
      rw [pc,calibrate_bootstrap_fetch]
      rfl
    simp only [step,fetched,Instruction.execute]
    rfl
  exact standalone_bits_linearControl (calibrationInput P) bootstrapCopyBody before middle after budget bootstrapCopy_straight fetch
    executed prefixes control ((prefixes.final executed).withPC _ (bounds.pc _ (by omega)))

end PDLower.CalibrationCompute
