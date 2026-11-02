module

public import Paid.RootD27Core_HeapCopyCell_032

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame PDCompute.Solver

def heapCopyNext (before : State) (source target remaining origin : ℕ) : State :=
  {heapCopyCellResult before source target remaining with pc:=origin}

/-- Actual nonempty copy iteration: fetched guard, six real copy/advance
instructions and fetched backedge. It writes only the ONE destination
cell, on every state of the same actual trace. -/
theorem heapCopy_step_actual (program : Program) (input : List Cell) (origin : ℕ)
    (before : State) (source target remaining : ℕ) (position : before.pc=origin)
    (address : before.register .address=.natural source) (fresh : before.register .fresh=.natural target)
    (index : before.register .index=.natural (remaining+1)) (live : source∈before.live)
    (fetched : FetchesCode program origin (heapCopyCode origin)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (heapCopyNext before source target remaining origin) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤150 ∧
      (∀ state∈trace,RegionMemory before state {target}) := by
  have guardFetch : program[origin]?=some (.branchZero .index (origin+8) (origin+1)) :=
    (fetched 0 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  have backFetch : program[origin+7]?=some (.jump origin) :=
    (fetched 7 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  let tested : State:={before with pc:=origin+1}
  let copied:=heapCopyCellResult tested source target remaining
  let after:=heapCopyNext before source target remaining origin
  have guard : step program input before=some tested := by
    simp [step,position,guardFetch,Instruction.execute,Cell.nat?,index,tested]
  have guardChain : [before,tested].IsChain (fun first later=>step program input first=some later) :=
    List.isChain_cons_cons.mpr ⟨guard,.singleton tested⟩
  have guardTime : time program [before,tested]≤30:=time_le_length program [before,tested]
  have cellFetch : FetchesCode program tested.pc heapCopyCellCode := by
    have inner:=fetched.append_left.append_right
    simpa only [List.length_cons,List.length_nil,Nat.add_zero] using inner
  obtain ⟨body,bh,bl,bc,bt,bm⟩:=heapCopyCell_actual program input tested source target remaining
    address fresh index live cellFetch
  have copiedPC : copied.pc=origin+7 := by
    change origin+1+6=origin+7
    omega
  have back : step program input copied=some after := by
    simp only [step,copiedPC,backFetch]
    rfl
  have controlled:=chain_append_control program input body copied after bc bl back
  have bodyMemory : ∀ state∈body++[after],RegionMemory tested state {target} := by
    intro state member
    rcases List.mem_append.mp member with proper|terminal
    · exact (bm state proper).region (by simp)
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      exact (heapCopyCell_result_memory before source target remaining).region (by simp)
  have guardMemory : ∀ state∈[before,tested],RegionMemory before state {target} := by
    intro state member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      exact .refl before _
    · subst state
      exact .refl before _
  have joined:=joinTrace_spec program input [before,tested] (body++[after]) before tested after
    30 120 rfl rfl (by
      have nonempty : body≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at bh
      simpa only [List.head?_append_of_ne_nil body nonempty] using bh)
      (by simp) guardChain controlled.1 guardTime (controlled.2.trans (by omega))
  exact ⟨joinTrace [before,tested] (body++[after]),joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    RegionMemory.join_trace _ _ before tested {target} rfl guardMemory bodyMemory⟩

/-- The real zero-counter guard reaches the literal indirect-return
instruction and fetches the saved return address; no free exit state. -/
theorem heapCopy_zero_actual (program : Program) (input : List Cell) (origin returnPC : ℕ)
    (before : State) (position : before.pc=origin) (index : before.register .index=.natural 0)
    (old : before.register .old=.natural returnPC) (fetched : FetchesCode program origin (heapCopyCode origin)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some {before with pc:=returnPC} ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤45 ∧
      (∀ region : Finset ℕ,∀ state∈trace,RegionMemory before state region) := by
  have guardFetch : program[origin]?=some (.branchZero .index (origin+8) (origin+1)) :=
    (fetched 0 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  have returnFetch : program[origin+8]?=some (.jumpIndirect .old) :=
    (fetched 8 (by rw [heapCopyCode_length];decide)).trans (by rfl)
  let tested : State:={before with pc:=origin+8}
  let after : State:={before with pc:=returnPC}
  have guard : step program input before=some tested := by
    simp [step,position,guardFetch,Instruction.execute,Cell.nat?,index,tested]
  have returned : step program input tested=some after := by
    simp [step,tested,returnFetch,Instruction.execute,Cell.nat?,old,after]
  refine ⟨[before,tested,after],rfl,rfl,
    List.isChain_cons_cons.mpr ⟨guard,List.isChain_cons_cons.mpr ⟨returned,.singleton after⟩⟩,
      time_le_length program [before,tested,after],?_⟩
  intro region state member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with same|same|same
  · subst state
    exact .refl before _
  · subst state
    exact .refl before _
  · subst state
    exact .refl before _

end RootD27.Core
