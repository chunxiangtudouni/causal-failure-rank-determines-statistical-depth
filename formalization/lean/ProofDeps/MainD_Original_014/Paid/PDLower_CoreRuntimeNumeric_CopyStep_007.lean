module

public import Paid.PDLower_CoreRuntimeNumeric_ArgumentsRestore_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)
open PDROC.CalibrationRow.Operand RootD27.Bits RootD27.Core

namespace PDLower.CoreRuntimeNumeric

/-- Raw six-op copier, distinct from the Header copySlot macro. Only
actual pointer successors need the independent address limit; the live
copied Cell and decreasing counter inherit SAME incoming B. -/
theorem copy_cell_prefix_safe (input : List Cell) (before : State)
    (source target remaining limit budget : ℕ)
    (address : before.register .address=.natural source) (fresh : before.register .fresh=.natural target)
    (index : before.register .index=.natural (remaining+1)) (live : source∈before.live)
    (safe : SafeBits before budget) (small : 2≤budget)
    (limitBits : (Cell.natural limit).bits≤budget) (sourceEnd : source+1≤limit) (targetEnd : target+1≤limit)
    (pcBits : natBits (before.pc+6)≤budget) : PrefixSafe input heapCopyCellCode before budget := by
  have scalar (value : ℕ) (bound : value≤limit) : (Cell.natural value).bits≤budget :=
    (Nat.add_le_add_left (natBits_mono bound) 1).trans limitBits
  have remainingBits : (Cell.natural remaining).bits≤budget := by
    have previous := safe.register .index
    rw [index] at previous
    exact (Nat.add_le_add_left (natBits_mono (by omega : remaining≤remaining+1)) 1).trans previous
  have targetBits : natBits target≤budget := by
    have bound := safe.register .fresh
    rw [fresh] at bound
    change 1+natBits target≤budget at bound
    omega
  have counter (n : ℕ) (bound : n≤6) : natBits (before.pc+n)≤budget :=
    (natBits_mono (by omega : before.pc+n≤before.pc+6)).trans pcBits
  let p1 := ({before with pc:=before.pc+1}).set .value (before.heap source)
  let p2 : State := {p1 with heap:=Function.update p1.heap target (p1.register .value),live:=insert target p1.live,pc:=p1.pc+1}
  let p3 := ({p2 with pc:=p2.pc+1}).set .total (.natural 1)
  let p4 := ({p3 with pc:=p3.pc+1}).set .address (.natural (source+1))
  let p5 := ({p4 with pc:=p4.pc+1}).set .fresh (.natural (target+1))
  let p6 := ({p5 with pc:=p5.pc+1}).set .index (.natural remaining)
  have s1 : SafeBits p1 budget := (safe.withPC _ (counter 1 (by decide))).set _ _ (safe.heap source live)
  have s2 : SafeBits p2 budget := (s1.withPC _ (counter 2 (by decide))).store target (p1.register .value) targetBits (s1.register .value)
  have s3 : SafeBits p3 budget :=
    (s2.withPC _ (by simpa only [p2,p1,State.set,Nat.add_assoc] using counter 3 (by decide))).set _ _ small
  have s4 : SafeBits p4 budget :=
    (s3.withPC _ (by simpa only [p3,p2,p1,State.set,Nat.add_assoc] using counter 4 (by decide))).set _ _ (scalar _ sourceEnd)
  have s5 : SafeBits p5 budget :=
    (s4.withPC _ (by simpa only [p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 5 (by decide))).set _ _ (scalar _ targetEnd)
  have s6 : SafeBits p6 budget :=
    (s5.withPC _ (by simpa only [p5,p4,p3,p2,p1,State.set,Nat.add_assoc] using counter 6 (by decide))).set _ _ remainingBits
  have e1 : (Instruction.load .value .address).execute input before=some p1 := by
    simp [Instruction.execute,p1,address,Cell.nat?,live]
  have e2 : (Instruction.store .fresh .value).execute input p1=some p2 := by
    simp [Instruction.execute,p1,p2,State.set,fresh,Cell.nat?]
  have e4 : (Instruction.natOp .add .address .address .total).execute input p3=some p4 := by
    simp [Instruction.execute,p4,p3,p2,p1,State.set,address,Cell.nat?,NatOp.eval]
  have e5 : (Instruction.natOp .add .fresh .fresh .total).execute input p4=some p5 := by
    simp [Instruction.execute,p5,p4,p3,p2,p1,State.set,fresh,Cell.nat?,NatOp.eval]
  have e6 : (Instruction.natOp .subtract .index .index .total).execute input p5=some p6 := by
    simp [Instruction.execute,p6,p5,p4,p3,p2,p1,State.set,index,Cell.nat?,NatOp.eval]
  apply PrefixSafe.cons input _ _ before p1 budget e1 safe
  apply PrefixSafe.cons input _ _ p1 p2 budget e2 s1
  apply PrefixSafe.cons input _ _ p2 p3 budget rfl s2
  apply PrefixSafe.cons input _ _ p3 p4 budget e4 s3
  apply PrefixSafe.cons input _ _ p4 p5 budget e5 s4
  apply PrefixSafe.cons input _ [] p5 p6 budget e6 s5
  exact PrefixSafe.nil input p6 budget s6

/-- One actual nonempty guard/copy/backedge, with joint memory, SAME B
and all PCs strictly inside the nine-op copy block. -/
theorem copy_step_resources (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (source target remaining limit budget : ℕ) (position : before.pc=origin)
    (address : before.register .address=.natural source) (fresh : before.register .fresh=.natural target)
    (index : before.register .index=.natural (remaining+1)) (live : source∈before.live)
    (safe : SafeBits before budget) (small : 2≤budget)
    (limitBits : (Cell.natural limit).bits≤budget) (sourceEnd : source+1≤limit) (targetEnd : target+1≤limit)
    (pcBits : natBits (origin+9)≤budget) (fetched : FetchesCode program origin (heapCopyCode origin)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (heapCopyNext before source target remaining origin) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤150 ∧
      (∀ state∈trace,RegionMemory before state {target} ∧ SafeBits state budget) ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc<origin+9) := by
  have guardFetch : program[origin]?=some (.branchZero .index (origin+8) (origin+1)) :=
    (fetched 0 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  have backFetch : program[origin+7]?=some (.jump origin) :=
    (fetched 7 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  let tested : State := {before with pc:=origin+1}
  let copied := heapCopyCellResult tested source target remaining
  let after := heapCopyNext before source target remaining origin
  have testedSafe : SafeBits tested budget := safe.withPC _ ((natBits_mono (by omega : origin+1≤origin+9)).trans pcBits)
  have guard : step program input before=some tested := by
    simp [step,position,guardFetch,Instruction.execute,Cell.nat?,index,tested]
  have guardChain : [before,tested].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨guard,.singleton tested⟩
  have cellFetch : FetchesCode program tested.pc heapCopyCellCode := by
    have inner := fetched.append_left.append_right
    simpa only [List.length_cons,List.length_nil,Nat.add_zero] using inner
  obtain ⟨body,bh,bl,bc,bt,bm,bodyPC,_proper,_peak⟩ :=
    linear_resources program input heapCopyCellCode tested copied {target} budget heapCopyCell_straight cellFetch
      (heapCopyCell_execute input tested source target remaining address fresh index live)
      (fun count bounded state actual => (heapCopyCell_prefix_memory input tested state source target remaining count
        address fresh index live (by simpa only [heapCopyCell_length] using bounded) actual).region (by simp))
      (copy_cell_prefix_safe input tested source target remaining limit budget address fresh index live testedSafe small
        limitBits sourceEnd targetEnd ((natBits_mono (by change origin+1+6≤origin+9;omega)).trans pcBits))
  have copiedPC : copied.pc=origin+7 := by change origin+1+6=origin+7;omega
  have back : step program input copied=some after := by simp only [step,copiedPC,backFetch];rfl
  have controlled := chain_append_control program input body copied after bc bl back
  have afterSafe : SafeBits after budget :=
    ((bm copied (List.mem_of_getLast? bl)).2).withPC origin ((natBits_mono (by omega : origin≤origin+9)).trans pcBits)
  have bodyProperties : ∀ state∈body++[after],RegionMemory tested state {target} ∧ SafeBits state budget := by
    intro state member
    rcases List.mem_append.mp member with proper|terminal
    · exact bm state proper
    · have same := List.mem_singleton.mp terminal
      subst state
      exact ⟨(heapCopyCell_result_memory before source target remaining).region (by simp),afterSafe⟩
  have guardProperties : ∀ state∈[before,tested],RegionMemory before state {target} ∧ SafeBits state budget := by
    intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state;exact ⟨.refl before _,safe⟩
    · subst state;exact ⟨.refl before _,testedSafe⟩
  have cellLength := heapCopyCell_length
  have joined := joinTrace_spec program input [before,tested] (body++[after]) before tested after 30 120 rfl rfl (by
      have nonempty : body≠[] := by intro empty;simp [empty] at bh
      simpa only [List.head?_append_of_ne_nil body nonempty] using bh)
    (by simp) guardChain controlled.1 (time_le_length program [before,tested]) (controlled.2.trans (by omega))
  have memory := RegionMemory.join_trace _ _ before tested {target} rfl
    (fun state member => (guardProperties state member).1) (fun state member => (bodyProperties state member).1)
  have allSafe := PDCompute.Pack.joinTrace_invariant [before,tested] (body++[after])
    (fun state => SafeBits state budget) (fun state member => (guardProperties state member).2)
    (fun state member => (bodyProperties state member).2)
  refine ⟨joinTrace [before,tested] (body++[after]),joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    (fun state member => ⟨memory state member,allSafe state member⟩),?_⟩
  intro state member
  rcases joinTrace_member member with guardMember|bodyMember
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at guardMember
    rcases guardMember with same|same
    · subst state;rw [position];omega
    · subst state;change origin≤origin+1 ∧ origin+1<origin+9;omega
  · rcases List.mem_append.mp bodyMember with earlier|terminal
    · have bounded := bodyPC state earlier
      change origin+1≤state.pc ∧ state.pc≤origin+1+6 at bounded
      omega
    · have same := List.mem_singleton.mp terminal
      subst state
      change origin≤origin ∧ origin<origin+9
      omega

/-- Real zero guard and actual indirect return, with no free exit. -/
theorem copy_zero_resources (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (budget : ℕ) (position : before.pc=origin)
    (index : before.register .index=.natural 0) (old : before.register .old=.natural (origin+9))
    (safe : SafeBits before budget) (pcBits : natBits (origin+9)≤budget)
    (fetched : FetchesCode program origin (heapCopyCode origin)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some {before with pc:=origin+9} ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤45 ∧
      (∀ region : Finset ℕ,∀ state∈trace,RegionMemory before state region ∧ SafeBits state budget) ∧
      (∀ state∈trace,origin≤state.pc ∧ state.pc≤origin+9) ∧
      (∀ state∈trace.dropLast,origin≤state.pc ∧ state.pc<origin+9) := by
  have guardFetch : program[origin]?=some (.branchZero .index (origin+8) (origin+1)) :=
    (fetched 0 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  have returnFetch : program[origin+8]?=some (.jumpIndirect .old) :=
    (fetched 8 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  let tested : State := {before with pc:=origin+8}
  let after : State := {before with pc:=origin+9}
  have guard : step program input before=some tested := by
    simp [step,position,guardFetch,Instruction.execute,Cell.nat?,index,tested]
  have returned : step program input tested=some after := by
    simp [step,tested,returnFetch,Instruction.execute,Cell.nat?,old,after]
  have testedSafe : SafeBits tested budget := safe.withPC _ ((natBits_mono (by omega : origin+8≤origin+9)).trans pcBits)
  have afterSafe : SafeBits after budget := safe.withPC _ pcBits
  refine ⟨[before,tested,after],rfl,rfl,
    List.isChain_cons_cons.mpr ⟨guard,List.isChain_cons_cons.mpr ⟨returned,.singleton after⟩⟩,
    time_le_length program [before,tested,after],?_,?_,?_⟩
  · intro region state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same|same
    · subst state;exact ⟨.refl before _,safe⟩
    · subst state;exact ⟨.refl before _,testedSafe⟩
    · subst state;exact ⟨.refl before _,afterSafe⟩
  · intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same|same
    · subst state;rw [position];omega
    · subst state;change origin≤origin+8 ∧ origin+8≤origin+9;omega
    · subst state;change origin≤origin+9 ∧ origin+9≤origin+9;omega
  · intro state member
    change state∈[before,tested] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state;rw [position];omega
    · subst state;change origin≤origin+8 ∧ origin+8<origin+9;omega

end PDLower.CoreRuntimeNumeric
