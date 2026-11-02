module

public import Paid.PDCompute_CoreSearchLoop_Code_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.CoreSearchLoop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame RootD27.Core

/-- Exactly one indexed obligation of the ORIGINAL global call refinement.
solveReturn remains the common callee epilogue, not a caller continuation. -/
def CallAt (program : Program) (labels : RoutineLabels) (P : Parameters) (fee : ℚ)
    (constant : ℕ) (states : List State) (index : ℕ) (state : State) : Prop :=
  ∃ multiplier : ℚ, (state.register .total).rat?=some multiplier ∧
    ∃ later final base,index<later ∧ states[later]?=some final ∧ final.pc=labels.solveReturn ∧
      (final.register .address).nat?=some base ∧
      let table:=P.cachedSolveMenuTable P.endpointCache fee multiplier P.tools P.certificate.stages
      (∀ offset<(encodeTable table).length,base+offset∈final.live) ∧
      heapSegment final base (encodeTable table).length=encodeTable table ∧
      time program ((states.drop index).take (later-index+1))≤
        constant*(P.certificate.stages+1)*(P.tools+1)*(P.certificate.M+1)

theorem CallAt.append_right {program : Program} {labels : RoutineLabels} {P : Parameters} {fee : ℚ}
    {constant : ℕ} {states : List State} {index : ℕ} {state : State}
    (window : CallAt program labels P fee constant states index state) (suffix : List State) :
    CallAt program labels P fee constant (states++suffix) index state := by
  obtain ⟨multiplier,total,later,final,base,order,returned,pc,address,live,table,cost⟩:=window
  have laterBound:=(List.getElem?_eq_some_iff.mp returned).1
  have indexBound : index<states.length:=by omega
  have interval : ((states++suffix).drop index).take (later-index+1)=
      (states.drop index).take (later-index+1):=by
    rw [List.drop_append_of_le_length indexBound.le]
    apply List.take_append_of_le_length
    simp only [List.length_drop]
    omega
  refine ⟨multiplier,total,later,final,base,order,?_,pc,address,live,table,?_⟩
  · rw [List.getElem?_append_left laterBound]
    exact returned
  · rw [interval]
    exact cost

theorem CallAt.prepend {program : Program} {labels : RoutineLabels} {P : Parameters} {fee : ℚ}
    {constant : ℕ} {states : List State} {index : ℕ} {state : State}
    (window : CallAt program labels P fee constant states index state) (front : List State) :
    CallAt program labels P fee constant (front++states) (front.length+index) state := by
  obtain ⟨multiplier,total,later,final,base,order,returned,pc,address,live,table,cost⟩:=window
  have difference : front.length+later-(front.length+index)+1=later-index+1:=by omega
  refine ⟨multiplier,total,front.length+later,final,base,by omega,?_,pc,address,live,table,?_⟩
  · rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]
    exact returned
  · rw [List.drop_length_add_append,difference]
    exact cost

/-- Dropping the first last state in joinTrace loses no prefix state:
the SAME actual middle state is present as the second trace's head. -/
theorem join_first_prefix (first later : List State) (middle : State)
    (last : first.getLast?=some middle) (head : later.head?=some middle) :
    ∃ suffix,joinTrace first later=first++suffix := by
  have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
  cases later with
  | nil => simp at head
  | cons state suffix =>
    have same : state=middle:=Option.some.inj head
    subst state
    refine ⟨suffix,?_⟩
    change first.dropLast++([middle]++suffix)=first++suffix
    rw [←List.append_assoc,split]

/-- Original solver windows embed in the SAME joined trace, with exact
sublist/time equality and shifted real indexes. No terminal-next-none,
fresh trace oracle, or caller-return substitution is required. -/
theorem refinement_join (program : Program) (labels : RoutineLabels) (P : Parameters) (fee : ℚ)
    (constant : ℕ) (first later : List State) (middle : State)
    (last : first.getLast?=some middle) (head : later.head?=some middle)
    (firstRefinement : SolverCallRefinement program labels P fee constant first)
    (laterRefinement : SolverCallRefinement program labels P fee constant later) :
    SolverCallRefinement program labels P fee constant (joinTrace first later) := by
  intro index state found position
  change CallAt program labels P fee constant (joinTrace first later) index state
  by_cases left : index<first.dropLast.length
  · obtain ⟨suffix,equal⟩:=join_first_prefix first later middle last head
    have short : index<first.length:=by
      have bound : first.dropLast.length≤first.length:=by simp only [List.length_dropLast];omega
      omega
    have earlier : first[index]?=some state:=by
      rw [equal,List.getElem?_append_left short] at found
      exact found
    have window : CallAt program labels P fee constant first index state:=firstRefinement index state earlier position
    rw [equal]
    exact window.append_right suffix
  · have right : first.dropLast.length ≤ index:=by omega
    have laterFound : later[index-first.dropLast.length]?=some state:=by
      change (first.dropLast++later)[index]?=some state at found
      rwa [List.getElem?_append_right right] at found
    have window : CallAt program labels P fee constant later (index-first.dropLast.length) state:=
      laterRefinement _ state laterFound position
    have lifted:=window.prepend first.dropLast
    have location : first.dropLast.length+(index-first.dropLast.length)=index:=by omega
    simpa only [joinTrace,location] using lifted

theorem refinement_of_no_entry (program : Program) (labels : RoutineLabels) (P : Parameters) (fee : ℚ)
    (constant : ℕ) (states : List State)
    (excluded : ∀ state∈states,state.pc≠labels.solveEntry) :
    SolverCallRefinement program labels P fee constant states := by
  intro index state found position
  exact False.elim (excluded state (List.mem_of_getElem? found) position)

theorem requests_dropLast (labels : RoutineLabels) (states : List State) (lastState : State)
    (last : states.getLast?=some lastState) (outside : lastState.pc≠labels.solveEntry) :
    actualSolveRequests labels states.dropLast=actualSolveRequests labels states := by
  have split:=List.dropLast_append_getLast? lastState (by rw [last];simp)
  have none : actualSolveRequests labels [lastState]=[]:=
    (no_solve_entry labels [lastState] (by
      intro state member
      have same : state=lastState:=List.mem_singleton.mp member
      subst state
      exact outside)).1
  have equal:=solveRequests_append labels states.dropLast [lastState]
  rw [split,none,List.append_nil] at equal
  exact equal.symm

theorem requests_join (labels : RoutineLabels) (first later : List State) (middle : State)
    (last : first.getLast?=some middle) (outside : middle.pc≠labels.solveEntry) :
    actualSolveRequests labels (joinTrace first later)=actualSolveRequests labels first++actualSolveRequests labels later := by
  change actualSolveRequests labels (first.dropLast++later)=_
  rw [solveRequests_append,requests_dropLast labels first middle last outside]

theorem entries_eq_requests_of_total (labels : RoutineLabels) (states : List State)
    (rational : ∀ state∈states,state.pc=labels.solveEntry → ∃ multiplier : ℚ,(state.register .total).rat?=some multiplier) :
    entryCount labels.solveEntry states=(actualSolveRequests labels states).length := by
  induction states with
  | nil => rfl
  | cons state states ih =>
    have tail : ∀ later∈states,later.pc=labels.solveEntry → ∃ multiplier : ℚ,(later.register .total).rat?=some multiplier:=
      fun later member=>rational later (List.mem_cons_of_mem _ member)
    have rest:=ih tail
    by_cases position : state.pc=labels.solveEntry
    · obtain ⟨multiplier,total⟩:=rational state (by simp) position
      simpa [entryCount,actualSolveRequests,position,total] using congrArg Nat.succ rest
    · simpa [entryCount,actualSolveRequests,position] using rest

/-- The original refinement itself certifies rational total at EVERY true
entry. Consequently no phantom entry is hidden by filterMap in the log. -/
theorem entries_eq_requests (program : Program) (labels : RoutineLabels) (P : Parameters) (fee : ℚ)
    (constant : ℕ) (states : List State)
    (refinement : SolverCallRefinement program labels P fee constant states) :
    entryCount labels.solveEntry states=(actualSolveRequests labels states).length := by
  apply entries_eq_requests_of_total labels states
  intro state member position
  obtain ⟨index,bound,equal⟩:=List.mem_iff_getElem.mp member
  have found : states[index]?=some state:=by rw [List.getElem?_eq_getElem bound,equal]
  obtain ⟨multiplier,total,_⟩:=refinement index state found position
  exact ⟨multiplier,total⟩

end PDCompute.CoreSearchLoop
