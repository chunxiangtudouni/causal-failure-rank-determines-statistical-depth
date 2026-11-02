module

public import Paid.PDROC_CoreOperands_002
public import Paid.RootD27Core_HeapSolverArguments_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CoreOperands

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits PDROC.CalibrationRow.Operand

/-- The first six ORIGINAL solver setup instructions really load M,
multiply it by2 and add99. Each physical prefix keeps caller B. -/
theorem solver_base_prefix_safe (input : List Cell) (before : State) (m budget : ℕ)
    (safe : SafeBits before budget) (live : 7∈before.live) (cell : before.heap 7=.natural m)
    (baseBits : (Cell.natural (99+2*m)).bits≤budget) (pcBits : natBits (before.pc+6)≤budget) :
    PrefixSafe input (RootD27.Core.solverHeapArgumentPrefix.take 6) before budget := by
  let p1 := ({before with pc:=before.pc+1}).set .address (.natural 7)
  let p2 := ({p1 with pc:=p1.pc+1}).set .fresh (.natural m)
  let p3 := ({p2 with pc:=p2.pc+1}).set .address (.natural 2)
  let p4 := ({p3 with pc:=p3.pc+1}).set .fresh (.natural (m*2))
  let p5 := ({p4 with pc:=p4.pc+1}).set .address (.natural 99)
  let p6 := ({p5 with pc:=p5.pc+1}).set .fresh (.natural (99+2*m))
  have scalar (n : ℕ) (bound : n≤99+2*m) : (Cell.natural n).bits≤budget := by
    exact (Nat.add_le_add_left (PDROC.DataBits.natBits_mono bound) 1).trans baseBits
  have counter (n : ℕ) (bound : n≤6) : natBits (before.pc+n)≤budget :=
    (PDROC.DataBits.natBits_mono (by omega : before.pc+n≤before.pc+6)).trans pcBits
  have mBits : (Cell.natural m).bits≤budget := by
    simpa only [cell] using safe.heap 7 live
  have s1 : SafeBits p1 budget := (safe.withPC _ (counter 1 (by decide))).set _ _ (scalar 7 (by omega))
  have s2 : SafeBits p2 budget :=
    (s1.withPC _ (by simpa only [p1,State.set,Nat.add_assoc] using counter 2 (by decide))).set _ _ mBits
  have s3 : SafeBits p3 budget :=
    (s2.withPC _ (by simpa only [p2,p1,State.set,Nat.add_assoc] using counter 3 (by decide))).set _ _ (scalar 2 (by omega))
  have s4 : SafeBits p4 budget :=
    (s3.withPC _ (by simpa only [p3,p2,p1,State.set,Nat.add_assoc] using counter 4 (by decide))).set _ _ (scalar (m*2) (by omega))
  have s5 : SafeBits p5 budget :=
    (s4.withPC _ (by simpa only [p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 5 (by decide))).set _ _ (scalar 99 (by omega))
  have s6 : SafeBits p6 budget :=
    (s5.withPC _ (by simpa only [p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 6 (by decide))).set _ _ baseBits
  have e2 : (Instruction.load .fresh .address).execute input p1=some p2 := by
    simp [Instruction.execute,p1,p2,State.set,Cell.nat?,live,cell]
  have fresh3 : p3.register .fresh=.natural m := by simp [p3,p2,State.set]
  have address3 : p3.register .address=.natural 2 := by simp [p3,State.set]
  have e4 : (Instruction.natOp .multiply .fresh .fresh .address).execute input p3=some p4 := by
    simp [Instruction.execute,fresh3,address3,Cell.nat?,NatOp.eval,p4]
  have fresh5 : p5.register .fresh=.natural (m*2) := by simp [p5,p4,State.set]
  have address5 : p5.register .address=.natural 99 := by simp [p5,State.set]
  have normalized : m*2+99=99+2*m := by omega
  have e6 : (Instruction.natOp .add .fresh .fresh .address).execute input p5=some p6 := by
    simp [Instruction.execute,fresh5,address5,Cell.nat?,NatOp.eval,normalized,p6]
  change PrefixSafe input [.constant .address (.natural 7),.load .fresh .address,
    .constant .address (.natural 2),.natOp .multiply .fresh .fresh .address,
    .constant .address (.natural 99),.natOp .add .fresh .fresh .address] before budget
  apply PrefixSafe.cons input _ _ before p1 budget rfl safe
  apply PrefixSafe.cons input _ _ p1 p2 budget e2 s1
  apply PrefixSafe.cons input _ _ p2 p3 budget rfl s2
  apply PrefixSafe.cons input _ _ p3 p4 budget e4 s3
  apply PrefixSafe.cons input _ _ p4 p5 budget rfl s4
  apply PrefixSafe.cons input _ [] p5 p6 budget e6 s5
  exact PrefixSafe.nil input p6 budget s6

end PDROC.CoreOperands
