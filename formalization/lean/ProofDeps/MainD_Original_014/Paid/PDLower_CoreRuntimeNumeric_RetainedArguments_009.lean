module

public import Paid.PDLower_CoreRuntimeNumeric_ArgumentsRestore_003
public import Paid.PDLower_CoreRuntimeNumeric_ControlRoom_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)
open PDROC.CalibrationRow.Operand RootD27.Bits RootD27.Core

namespace PDLower.CoreRuntimeNumeric

/-- Genuine save/read/count/buffer-address arithmetic, using a fixed
independent cap and preserving arbitrary old scratch at SAME B. -/
theorem retained_arguments_prefix_safe (input : List Cell) (before : State)
    (base n k source count returnPC budget : ℕ) (upper : Bool)
    (fresh : before.register .fresh=.natural base) (address : before.register .address=.natural source)
    (index : before.register .index=.natural count) (nLive : 0∈before.live) (kLive : 1∈before.live)
    (nValue : before.heap 0=.natural n) (kValue : before.heap 1=.natural k)
    (safe : SafeBits before budget) (baseLower : 99≤base)
    (limitBits : (Cell.natural (base+78*PDCompute.Solver.entryCount n k)).bits≤budget)
    (returnBits : (Cell.natural returnPC).bits≤budget) (pcBits : natBits (before.pc+20)≤budget) :
    PrefixSafe input (retainedArgumentsCode upper returnPC) before budget := by
  let E := PDCompute.Solver.entryCount n k
  let coefficient : ℕ := if upper then 70 else 62
  have positive : 1≤E := by change 0<(n+1)*(k+1);positivity
  have rows : n+1≤E := by
    have bound := Nat.mul_le_mul_left (n+1) (by omega : 1≤k+1)
    simpa only [E,PDCompute.Solver.entryCount,Nat.mul_one] using bound
  have columns : k+1≤E := by
    have bound := Nat.mul_le_mul_right (k+1) (by omega : 1≤n+1)
    simpa only [E,PDCompute.Solver.entryCount,Nat.one_mul] using bound
  have coefficientBound : coefficient≤70 := by cases upper <;> decide
  have scaled : coefficient*E≤70*E := Nat.mul_le_mul_right E coefficientBound
  have scalar (value : ℕ) (bound : value≤base+78*E) : (Cell.natural value).bits≤budget :=
    (Nat.add_le_add_left (natBits_mono bound) 1).trans limitBits
  have counter (j : ℕ) (bound : j≤20) : natBits (before.pc+j)≤budget :=
    (natBits_mono (by omega : before.pc+j≤before.pc+20)).trans pcBits
  have sourceBits : (Cell.natural source).bits≤budget := by simpa only [address] using safe.register .address
  have countBits : (Cell.natural count).bits≤budget := by simpa only [index] using safe.register .index
  have nBits : (Cell.natural n).bits≤budget := by simpa only [nValue] using safe.heap 0 nLive
  have kBits : (Cell.natural k).bits≤budget := by simpa only [kValue] using safe.heap 1 kLive
  let p1 := ({before with pc:=before.pc+1}).set .total (.natural 46)
  let p2 : State := {p1 with heap:=Function.update p1.heap 46 (p1.register .address),live:=insert 46 p1.live,pc:=p1.pc+1}
  let p3 := ({p2 with pc:=p2.pc+1}).set .total (.natural 47)
  let p4 : State := {p3 with heap:=Function.update p3.heap 47 (p3.register .index),live:=insert 47 p3.live,pc:=p3.pc+1}
  let p5 := ({p4 with pc:=p4.pc+1}).set .address (.natural 0)
  let p6 := ({p5 with pc:=p5.pc+1}).set .total (.natural n)
  let p7 := ({p6 with pc:=p6.pc+1}).set .flag (.natural 1)
  let p8 := ({p7 with pc:=p7.pc+1}).set .total (.natural (n+1))
  let p9 := ({p8 with pc:=p8.pc+1}).set .address (.natural 1)
  let p10 := ({p9 with pc:=p9.pc+1}).set .value (.natural k)
  let p11 := ({p10 with pc:=p10.pc+1}).set .value (.natural (k+1))
  let p12 := ({p11 with pc:=p11.pc+1}).set .total (.natural E)
  let p13 := ({p12 with pc:=p12.pc+1}).set .value (.natural coefficient)
  let p14 := ({p13 with pc:=p13.pc+1}).set .total (.natural (coefficient*E))
  let p15 := ({p14 with pc:=p14.pc+1}).set .fresh (.natural (base+coefficient*E))
  let p16 := ({p15 with pc:=p15.pc+1}).set .address (.natural 46)
  let p17 := ({p16 with pc:=p16.pc+1}).set .address (.natural source)
  let p18 := ({p17 with pc:=p17.pc+1}).set .value (.natural 47)
  let p19 := ({p18 with pc:=p18.pc+1}).set .index (.natural count)
  let p20 := ({p19 with pc:=p19.pc+1}).set .old (.natural returnPC)
  have s1 : SafeBits p1 budget := (safe.withPC _ (counter 1 (by decide))).set .total (.natural 46) (scalar 46 (by omega))
  have s2 : SafeBits p2 budget := (s1.withPC _ (by simpa only [p1,State.set,Nat.add_assoc] using counter 2 (by decide))).store 46 (p1.register .address)
    (by have bound := scalar 46 (by omega);change 1+natBits 46≤budget at bound;omega) (s1.register .address)
  have s3 : SafeBits p3 budget := (s2.withPC _ (by simpa only [p2,p1,State.set,Nat.add_assoc] using counter 3 (by decide))).set .total (.natural 47) (scalar 47 (by omega))
  have s4 : SafeBits p4 budget := (s3.withPC _ (by simpa only [p3,p2,p1,State.set,Nat.add_assoc] using counter 4 (by decide))).store 47 (p3.register .index)
    (by have bound := scalar 47 (by omega);change 1+natBits 47≤budget at bound;omega) (s3.register .index)
  have s5 : SafeBits p5 budget := (s4.withPC _ (by simpa only [p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 5 (by decide))).set .address (.natural 0) (scalar 0 (by omega))
  have s6 : SafeBits p6 budget := (s5.withPC _ (by simpa only [p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 6 (by decide))).set .total (.natural n) (nBits)
  have s7 : SafeBits p7 budget := (s6.withPC _ (by simpa only [p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 7 (by decide))).set .flag (.natural 1) (scalar 1 (by omega))
  have s8 : SafeBits p8 budget := (s7.withPC _ (by simpa only [p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 8 (by decide))).set .total (.natural (n+1)) (scalar (n+1) (by omega))
  have s9 : SafeBits p9 budget := (s8.withPC _ (by simpa only [p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 9 (by decide))).set .address (.natural 1) (scalar 1 (by omega))
  have s10 : SafeBits p10 budget := (s9.withPC _ (by simpa only [p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 10 (by decide))).set .value (.natural k) (kBits)
  have s11 : SafeBits p11 budget := (s10.withPC _ (by simpa only [p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 11 (by decide))).set .value (.natural (k+1)) (scalar (k+1) (by omega))
  have s12 : SafeBits p12 budget := (s11.withPC _ (by simpa only [p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 12 (by decide))).set .total (.natural E) (scalar E (by omega))
  have s13 : SafeBits p13 budget := (s12.withPC _ (by simpa only [p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 13 (by decide))).set .value (.natural coefficient) (scalar coefficient (by omega))
  have s14 : SafeBits p14 budget := (s13.withPC _ (by simpa only [p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 14 (by decide))).set .total (.natural (coefficient*E)) (scalar (coefficient*E) (by omega))
  have s15 : SafeBits p15 budget := (s14.withPC _ (by simpa only [p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 15 (by decide))).set .fresh (.natural (base+coefficient*E)) (scalar (base+coefficient*E) (by omega))
  have s16 : SafeBits p16 budget := (s15.withPC _ (by simpa only [p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 16 (by decide))).set .address (.natural 46) (scalar 46 (by omega))
  have s17 : SafeBits p17 budget := (s16.withPC _ (by simpa only [p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 17 (by decide))).set .address (.natural source) (sourceBits)
  have s18 : SafeBits p18 budget := (s17.withPC _ (by simpa only [p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 18 (by decide))).set .value (.natural 47) (scalar 47 (by omega))
  have s19 : SafeBits p19 budget := (s18.withPC _ (by simpa only [p18,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 19 (by decide))).set .index (.natural count) (countBits)
  have s20 : SafeBits p20 budget := (s19.withPC _ (by simpa only [p19,p18,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 20 (by decide))).set .old (.natural returnPC) (returnBits)
  have e1 : (Instruction.constant .total (.natural 46)).execute input before=some p1 := rfl
  have e2 : (Instruction.store .total .address).execute input p1=some p2 := by simp [Instruction.execute,p2,p1,State.set,Cell.nat?,address]
  have e3 : (Instruction.constant .total (.natural 47)).execute input p2=some p3 := rfl
  have e4 : (Instruction.store .total .index).execute input p3=some p4 := by simp [Instruction.execute,p4,p3,p2,p1,State.set,Cell.nat?,index]
  have e5 : (Instruction.constant .address (.natural 0)).execute input p4=some p5 := rfl
  have e6 : (Instruction.load .total .address).execute input p5=some p6 := by simp [Instruction.execute,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,nLive,nValue]
  have e7 : (Instruction.constant .flag (.natural 1)).execute input p6=some p7 := rfl
  have e8 : (Instruction.natOp .add .total .total .flag).execute input p7=some p8 := by simp [Instruction.execute,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval]
  have e9 : (Instruction.constant .address (.natural 1)).execute input p8=some p9 := rfl
  have e10 : (Instruction.load .value .address).execute input p9=some p10 := by simp [Instruction.execute,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,kLive,kValue]
  have e11 : (Instruction.natOp .add .value .value .flag).execute input p10=some p11 := by simp [Instruction.execute,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval]
  have e12 : (Instruction.natOp .multiply .total .total .value).execute input p11=some p12 := by simp [Instruction.execute,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval,E,PDCompute.Solver.entryCount]
  have e13 : (Instruction.constant .value (.natural (if upper then 70 else 62))).execute input p12=some p13 := rfl
  have e14 : (Instruction.natOp .multiply .total .total .value).execute input p13=some p14 := by simp [Instruction.execute,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval,Nat.mul_comm]
  have e15 : (Instruction.natOp .add .fresh .fresh .total).execute input p14=some p15 := by simp [Instruction.execute,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval,fresh]
  have e16 : (Instruction.constant .address (.natural 46)).execute input p15=some p16 := rfl
  have e17 : (Instruction.load .address .address).execute input p16=some p17 := by simp [Instruction.execute,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,address]
  have e18 : (Instruction.constant .value (.natural 47)).execute input p17=some p18 := rfl
  have e19 : (Instruction.load .index .value).execute input p18=some p19 := by simp [Instruction.execute,p19,p18,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,index]
  have e20 : (Instruction.constant .old (.natural returnPC)).execute input p19=some p20 := rfl
  change PrefixSafe input [.constant .total (.natural 46),.store .total .address,.constant .total (.natural 47),.store .total .index,.constant .address (.natural 0),.load .total .address,.constant .flag (.natural 1),.natOp .add .total .total .flag,.constant .address (.natural 1),.load .value .address,.natOp .add .value .value .flag,.natOp .multiply .total .total .value,.constant .value (.natural (if upper then 70 else 62)),.natOp .multiply .total .total .value,.natOp .add .fresh .fresh .total,.constant .address (.natural 46),.load .address .address,.constant .value (.natural 47),.load .index .value,.constant .old (.natural returnPC)] before budget
  apply PrefixSafe.cons input _ _ before p1 budget e1 safe
  apply PrefixSafe.cons input _ _ p1 p2 budget e2 s1
  apply PrefixSafe.cons input _ _ p2 p3 budget e3 s2
  apply PrefixSafe.cons input _ _ p3 p4 budget e4 s3
  apply PrefixSafe.cons input _ _ p4 p5 budget e5 s4
  apply PrefixSafe.cons input _ _ p5 p6 budget e6 s5
  apply PrefixSafe.cons input _ _ p6 p7 budget e7 s6
  apply PrefixSafe.cons input _ _ p7 p8 budget e8 s7
  apply PrefixSafe.cons input _ _ p8 p9 budget e9 s8
  apply PrefixSafe.cons input _ _ p9 p10 budget e10 s9
  apply PrefixSafe.cons input _ _ p10 p11 budget e11 s10
  apply PrefixSafe.cons input _ _ p11 p12 budget e12 s11
  apply PrefixSafe.cons input _ _ p12 p13 budget e13 s12
  apply PrefixSafe.cons input _ _ p13 p14 budget e14 s13
  apply PrefixSafe.cons input _ _ p14 p15 budget e15 s14
  apply PrefixSafe.cons input _ _ p15 p16 budget e16 s15
  apply PrefixSafe.cons input _ _ p16 p17 budget e17 s16
  apply PrefixSafe.cons input _ _ p17 p18 budget e18 s17
  apply PrefixSafe.cons input _ _ p18 p19 budget e19 s18
  apply PrefixSafe.cons input _ [] p19 p20 budget e20 s19
  exact PrefixSafe.nil input p20 budget s20

end PDLower.CoreRuntimeNumeric
