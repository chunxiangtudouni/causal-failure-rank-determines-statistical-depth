module

public import Paid.PDLower_CoreRuntimeNumeric_ArgumentsRestore_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)
open PDROC.CalibrationRow.Operand RootD27.Bits

namespace PDLower.CoreRuntimeNumeric

/-- The real twenty instructions read the three live dense root cells.
Their rational bits come from incoming SafeBits, not from a statistics
oracle. The returned pointer/count are never replaced by assumptions. -/
theorem statistics_prefix_safe (input : List Cell) (before : State)
    (target source menu budget : ℕ) (observation repairs failure : ℚ)
    (lower : 13≤target) (upper : target+2<46) (sourceBound : 51≤source)
    (address : before.register .address=.natural source)
    (root : HeapList before (source-3) [.rational observation,.rational repairs,.rational failure])
    (menuLive : 7∈before.live) (menuValue : before.heap 7=.natural menu)
    (safe : SafeBits before budget) (small : 7≤budget)
    (baseBits : (Cell.natural (99+2*menu)).bits≤budget) (pcBits : natBits (before.pc+20)≤budget) :
    PrefixSafe input (RootD27.Core.rootStatisticsCode target) before budget := by
  have sourceBits : (Cell.natural source).bits≤budget := by simpa only [address] using safe.register .address
  have sourceCell (value : ℕ) (bound : value≤source) : (Cell.natural value).bits≤budget :=
    (Nat.add_le_add_left (natBits_mono bound) 1).trans sourceBits
  have baseCell (value : ℕ) (bound : value≤99+2*menu) : (Cell.natural value).bits≤budget :=
    (Nat.add_le_add_left (natBits_mono bound) 1).trans baseBits
  have fixed (value : ℕ) (bound : value<46) : (Cell.natural value).bits≤budget :=
    ((Nat.add_le_add_left (natBits_mono (by omega : value≤47)) 1).trans (show 1+natBits 47≤7 by decide)).trans small
  have counter (n : ℕ) (bound : n≤20) : natBits (before.pc+n)≤budget :=
    (natBits_mono (by omega : before.pc+n≤before.pc+20)).trans pcBits
  have ol := root.1 0 (by change 0<3;decide)
  have rl := root.1 1 (by change 1<3;decide)
  have fl := root.1 2 (by change 2<3;decide)
  have ov := HeapList.value root 0 (by change 0<3;decide)
  have rv := HeapList.value root 1 (by change 1<3;decide)
  have fv := HeapList.value root 2 (by change 2<3;decide)
  simp only [Nat.add_zero,List.getElem_cons_zero,List.getElem_cons_succ] at ol ov rv fv
  have ob : (Cell.rational observation).bits≤budget := by simpa only [ov] using safe.heap (source-3) ol
  have rb : (Cell.rational repairs).bits≤budget := by simpa only [rv] using safe.heap (source-3+1) rl
  have fb : (Cell.rational failure).bits≤budget := by simpa only [fv] using safe.heap (source-3+2) fl
  have mb : (Cell.natural menu).bits≤budget := by simpa only [menuValue] using safe.heap 7 menuLive
  have r1 : source-3+1≠target := by omega
  have r2 : source-3+2≠target := by omega
  have q2 : source-3+2≠target+1 := by omega
  have t0 : 7≠target := by omega
  have t1 : 7≠target+1 := by omega
  have t2 : 7≠target+2 := by omega
  have arithmetic : menu*2+99=99+2*menu := by omega
  let p1 := ({before with pc:=before.pc+1}).set .total (.natural 3)
  let p2 := ({p1 with pc:=p1.pc+1}).set .total (.natural (source-3))
  let p3 := ({p2 with pc:=p2.pc+1}).set .flag (.rational observation)
  let p4 := ({p3 with pc:=p3.pc+1}).set .fresh (.natural target)
  let p5 : State := {p4 with heap:=Function.update p4.heap (target) (p4.register .flag),live:=insert (target) p4.live,pc:=p4.pc+1}
  let p6 := ({p5 with pc:=p5.pc+1}).set .value (.natural 1)
  let p7 := ({p6 with pc:=p6.pc+1}).set .total (.natural (source-3+1))
  let p8 := ({p7 with pc:=p7.pc+1}).set .flag (.rational repairs)
  let p9 := ({p8 with pc:=p8.pc+1}).set .fresh (.natural (target+1))
  let p10 : State := {p9 with heap:=Function.update p9.heap (target+1) (p9.register .flag),live:=insert (target+1) p9.live,pc:=p9.pc+1}
  let p11 := ({p10 with pc:=p10.pc+1}).set .total (.natural (source-3+2))
  let p12 := ({p11 with pc:=p11.pc+1}).set .flag (.rational failure)
  let p13 := ({p12 with pc:=p12.pc+1}).set .fresh (.natural (target+2))
  let p14 : State := {p13 with heap:=Function.update p13.heap (target+2) (p13.register .flag),live:=insert (target+2) p13.live,pc:=p13.pc+1}
  let p15 := ({p14 with pc:=p14.pc+1}).set .flag (.natural 7)
  let p16 := ({p15 with pc:=p15.pc+1}).set .fresh (.natural menu)
  let p17 := ({p16 with pc:=p16.pc+1}).set .total (.natural 2)
  let p18 := ({p17 with pc:=p17.pc+1}).set .fresh (.natural (menu*2))
  let p19 := ({p18 with pc:=p18.pc+1}).set .total (.natural 99)
  let p20 := ({p19 with pc:=p19.pc+1}).set .fresh (.natural (99+2*menu))
  have s1 : SafeBits p1 budget := (safe.withPC _ (counter 1 (by decide))).set .total (.natural 3) (fixed 3 (by decide))
  have s2 : SafeBits p2 budget := (s1.withPC _ (by simpa only [p1,State.set,Nat.add_assoc] using counter 2 (by decide))).set .total (.natural (source-3)) (sourceCell (source-3) (by omega))
  have s3 : SafeBits p3 budget := (s2.withPC _ (by simpa only [p2,p1,State.set,Nat.add_assoc] using counter 3 (by decide))).set .flag (.rational observation) (ob)
  have s4 : SafeBits p4 budget := (s3.withPC _ (by simpa only [p3,p2,p1,State.set,Nat.add_assoc] using counter 4 (by decide))).set .fresh (.natural target) (fixed target (by omega))
  have s5 : SafeBits p5 budget := (s4.withPC _ (by simpa only [p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 5 (by decide))).store (target) (p4.register .flag)
    (by have bound := fixed (target) (by omega);change 1+natBits (target)≤budget at bound;omega) (s4.register .flag)
  have s6 : SafeBits p6 budget := (s5.withPC _ (by simpa only [p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 6 (by decide))).set .value (.natural 1) (fixed 1 (by decide))
  have s7 : SafeBits p7 budget := (s6.withPC _ (by simpa only [p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 7 (by decide))).set .total (.natural (source-3+1)) (sourceCell (source-3+1) (by omega))
  have s8 : SafeBits p8 budget := (s7.withPC _ (by simpa only [p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 8 (by decide))).set .flag (.rational repairs) (rb)
  have s9 : SafeBits p9 budget := (s8.withPC _ (by simpa only [p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 9 (by decide))).set .fresh (.natural (target+1)) (fixed (target+1) (by omega))
  have s10 : SafeBits p10 budget := (s9.withPC _ (by simpa only [p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 10 (by decide))).store (target+1) (p9.register .flag)
    (by have bound := fixed (target+1) (by omega);change 1+natBits (target+1)≤budget at bound;omega) (s9.register .flag)
  have s11 : SafeBits p11 budget := (s10.withPC _ (by simpa only [p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 11 (by decide))).set .total (.natural (source-3+2)) (sourceCell (source-3+2) (by omega))
  have s12 : SafeBits p12 budget := (s11.withPC _ (by simpa only [p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 12 (by decide))).set .flag (.rational failure) (fb)
  have s13 : SafeBits p13 budget := (s12.withPC _ (by simpa only [p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 13 (by decide))).set .fresh (.natural (target+2)) (fixed (target+2) (by omega))
  have s14 : SafeBits p14 budget := (s13.withPC _ (by simpa only [p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 14 (by decide))).store (target+2) (p13.register .flag)
    (by have bound := fixed (target+2) (by omega);change 1+natBits (target+2)≤budget at bound;omega) (s13.register .flag)
  have s15 : SafeBits p15 budget := (s14.withPC _ (by simpa only [p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 15 (by decide))).set .flag (.natural 7) (fixed 7 (by decide))
  have s16 : SafeBits p16 budget := (s15.withPC _ (by simpa only [p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 16 (by decide))).set .fresh (.natural menu) (mb)
  have s17 : SafeBits p17 budget := (s16.withPC _ (by simpa only [p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 17 (by decide))).set .total (.natural 2) (fixed 2 (by decide))
  have s18 : SafeBits p18 budget := (s17.withPC _ (by simpa only [p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 18 (by decide))).set .fresh (.natural (menu*2)) (baseCell (menu*2) (by omega))
  have s19 : SafeBits p19 budget := (s18.withPC _ (by simpa only [p18,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 19 (by decide))).set .total (.natural 99) (baseCell 99 (by omega))
  have s20 : SafeBits p20 budget := (s19.withPC _ (by simpa only [p19,p18,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 20 (by decide))).set .fresh (.natural (99+2*menu)) (baseBits)
  have e1 : (Instruction.constant .total (.natural 3)).execute input before=some p1 := rfl
  have e2 : (Instruction.natOp .subtract .total .address .total).execute input p1=some p2 := by simp [Instruction.execute,p2,p1,State.set,Cell.nat?,NatOp.eval,address]
  have e3 : (Instruction.load .flag .total).execute input p2=some p3 := by simp [Instruction.execute,p3,p2,p1,State.set,Cell.nat?,ol,ov]
  have e4 : (Instruction.constant .fresh (.natural target)).execute input p3=some p4 := rfl
  have e5 : (Instruction.store .fresh .flag).execute input p4=some p5 := by simp [Instruction.execute,p5,p4,p3,p2,p1,State.set,Cell.nat?]
  have e6 : (Instruction.constant .value (.natural 1)).execute input p5=some p6 := rfl
  have e7 : (Instruction.natOp .add .total .total .value).execute input p6=some p7 := by simp [Instruction.execute,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval]
  have e8 : (Instruction.load .flag .total).execute input p7=some p8 := by simp [Instruction.execute,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,rl,rv,r1]
  have e9 : (Instruction.constant .fresh (.natural (target+1))).execute input p8=some p9 := rfl
  have e10 : (Instruction.store .fresh .flag).execute input p9=some p10 := by simp [Instruction.execute,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?]
  have e11 : (Instruction.natOp .add .total .total .value).execute input p10=some p11 := by simp [Instruction.execute,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval]
  have e12 : (Instruction.load .flag .total).execute input p11=some p12 := by simp [Instruction.execute,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,fl,fv,r2,q2]
  have e13 : (Instruction.constant .fresh (.natural (target+2))).execute input p12=some p13 := rfl
  have e14 : (Instruction.store .fresh .flag).execute input p13=some p14 := by simp [Instruction.execute,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?]
  have e15 : (Instruction.constant .flag (.natural 7)).execute input p14=some p15 := rfl
  have e16 : (Instruction.load .fresh .flag).execute input p15=some p16 := by simp [Instruction.execute,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,menuLive,menuValue,t0,t1,t2]
  have e17 : (Instruction.constant .total (.natural 2)).execute input p16=some p17 := rfl
  have e18 : (Instruction.natOp .multiply .fresh .fresh .total).execute input p17=some p18 := by simp [Instruction.execute,p18,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval]
  have e19 : (Instruction.constant .total (.natural 99)).execute input p18=some p19 := rfl
  have e20 : (Instruction.natOp .add .fresh .fresh .total).execute input p19=some p20 := by simp [Instruction.execute,p20,p19,p18,p17,p16,p15,p14,p13,p12,p11,p10,p9,p8,p7,p6,p5,p4,p3,p2,p1,State.set,Cell.nat?,NatOp.eval,arithmetic]
  change PrefixSafe input [.constant .total (.natural 3),.natOp .subtract .total .address .total,.load .flag .total,.constant .fresh (.natural target),.store .fresh .flag,.constant .value (.natural 1),.natOp .add .total .total .value,.load .flag .total,.constant .fresh (.natural (target+1)),.store .fresh .flag,.natOp .add .total .total .value,.load .flag .total,.constant .fresh (.natural (target+2)),.store .fresh .flag,.constant .flag (.natural 7),.load .fresh .flag,.constant .total (.natural 2),.natOp .multiply .fresh .fresh .total,.constant .total (.natural 99),.natOp .add .fresh .fresh .total] before budget
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

theorem statistics_resources (program : Program) (input : List Cell) (before : State)
    (target source menu budget : ℕ) (observation repairs failure : ℚ)
    (lower : 13≤target) (upper : target+2<46) (sourceBound : 51≤source)
    (address : before.register .address=.natural source)
    (root : HeapList before (source-3) [.rational observation,.rational repairs,.rational failure])
    (menuLive : 7∈before.live) (menuValue : before.heap 7=.natural menu)
    (safe : SafeBits before budget) (small : 7≤budget)
    (baseBits : (Cell.natural (99+2*menu)).bits≤budget) (pcBits : natBits (before.pc+20)≤budget)
    (fetched : FetchesCode program before.pc (RootD27.Core.rootStatisticsCode target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (RootD27.Core.rootStatisticsResult before target menu observation repairs failure) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤315 ∧
      (∀ state∈trace,RegionMemory before state {target,target+1,target+2} ∧ SafeBits state budget) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+20) ∧
      (∀ state∈trace.dropLast,state.pc<before.pc+20) ∧ peakCells trace≤workingCells before+3 := by
  have run := RootD27.Core.rootStatistics_execute input before target source menu observation repairs failure
    lower upper sourceBound address root menuLive menuValue
  obtain ⟨trace,head,last,chain,cost,properties,location,proper,space⟩ :=
    linear_resources program input _ before _ {target,target+1,target+2} budget
      (RootD27.Core.rootStatistics_straight target) fetched run
      (fun steps bounded state actual => RootD27.Core.rootStatistics_prefix_memory input before state target source menu steps
        observation repairs failure lower upper sourceBound address root menuLive menuValue
        (by simpa only [RootD27.Core.rootStatistics_length] using bounded) actual)
      (statistics_prefix_safe input before target source menu budget observation repairs failure lower upper sourceBound address
        root menuLive menuValue safe small baseBits pcBits)
  have notFirst : target∉({target+1,target+2} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton];omega
  have notSecond : target+1∉({target+2} : Finset ℕ) := by simp only [Finset.mem_singleton];omega
  have card : ({target,target+1,target+2}:Finset ℕ).card=3 := by
    rw [Finset.card_insert_of_notMem notFirst,Finset.card_insert_of_notMem notSecond,Finset.card_singleton]
  exact ⟨trace,head,last,chain,by simpa only [RootD27.Core.rootStatistics_length] using cost,properties,
    by simpa only [RootD27.Core.rootStatistics_length] using location,
    by simpa only [RootD27.Core.rootStatistics_length] using proper,by simpa only [card] using space⟩

end PDLower.CoreRuntimeNumeric
