module
public import Paid.PDROC_BitVM_Log_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
@[expose] public section
namespace PDROC.BitVM.VM.BoundaryBudget
open PaperProofs.Paid.Computation PaperProofs.Paid.Parameters
open PDROC.BitVM.Log

/-- Chronological events of the actual successful transitions BEFORE the
last source boundary. This is determined by the trace, not an arbitrary
history chosen merely because it has the same heap/live interpretation. -/
def actualHistory (program : Program) (states : List State) : List HeapEvent :=
  states.dropLast.flatMap (stepEvents program)

theorem actualHistory_cons_cons (program : Program) (before next : State) (rest : List State) :
    actualHistory program (before::next::rest)=stepEvents program before++actualHistory program (next::rest) := by
  simp only [actualHistory,List.dropLast_cons_cons,List.flatMap_cons]

theorem actualHistory_append (program : Program) (states : List State) (before next : State)
    (last : states.getLast?=some before) :
    actualHistory program (states++[next])=actualHistory program states++stepEvents program before := by
  have split:=List.dropLast_append_getLast? before (by rw [last];simp)
  have mapped:=congrArg (List.flatMap (stepEvents program)) split
  simp only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil] at mapped
  simp only [actualHistory,List.dropLast_concat]
  exact mapped.symm

theorem time_append (program : Program) (first later : List State) :
    time program (first++later)=time program first+time program later := by
  simp only [time,primitiveTrace,List.flatMap_append,List.length_append]

theorem time_take_le (program : Program) (states : List State) (count : ℕ) :
    time program (states.take count)≤time program states := by
  have split:=time_append program (states.take count) (states.drop count)
  rw [List.take_append_drop] at split
  omega

theorem actualHistory_count (program : Program) (states : List State) :
    (actualHistory program states).length≤time program states := by
  induction states with
  | nil => simp [actualHistory]
  | cons before rest ih =>
    cases rest with
    | nil => simp [actualHistory]
    | cons next rest =>
      rw [actualHistory_cons_cons,List.length_append]
      have cost:=stepEvents_cost program before
      simp only [time,primitiveTrace,List.flatMap_cons,List.length_append] at ih ⊢
      exact Nat.add_le_add cost ih

theorem actualHistory_event_bounds (program : Program) (states : List State) (budget : ℕ)
    (allBits : ∀ current∈states,∀ size∈stateCellBits current,size≤budget) :
    ∀ event∈actualHistory program states,(encodeEvent event).length≤4*budget+2 := by
  intro event member
  obtain ⟨current,currentMember,eventMember⟩:=List.mem_flatMap.mp member
  exact stepEvents_bounded program current budget
    (allBits current (List.mem_of_mem_dropLast currentMember)) event eventMember

theorem actualHistory_encoded_bound (program : Program) (states : List State) (budget : ℕ)
    (allBits : ∀ current∈states,∀ size∈stateCellBits current,size≤budget) :
    (encodeHistory (actualHistory program states)).length≤time program states*(4*budget+2) :=
  (encodeHistory_length _ budget (actualHistory_event_bounds program states budget allBits)).trans
    (Nat.mul_le_mul_right _ (actualHistory_count program states))

/-- Unlike a bare existential Refines witness, this is the exact empty
history plus the actual store/release events, in actual execution order. -/
theorem actualHistory_refines (program : Program) (input : List Cell)
    (before : State) (rest : List State) (events : List HeapEvent)
    (chain : (before::rest).IsChain (fun a b=>step program input a=some b))
    (represented : Refines events before) :
    Refines (events++actualHistory program (before::rest)) ((before::rest).getLast (by simp)) := by
  induction rest generalizing before events with
  | nil => simpa only [actualHistory,List.dropLast_singleton,List.flatMap_nil,List.append_nil,List.getLast_singleton] using represented
  | cons next rest ih =>
    have edge:=(List.isChain_cons_cons.mp chain).1
    have continued:=ih next (events++stepEvents program before) chain.tail
      (step_refines program input events before next represented edge)
    simpa only [actualHistory_cons_cons,List.append_assoc,List.getLast_cons_cons] using continued

theorem initial_actualHistory_refines (program : Program) (input : List Cell) (rest : List State)
    (chain : (initial::rest).IsChain (fun a b=>step program input a=some b)) :
    Refines (actualHistory program (initial::rest)) ((initial::rest).getLast (by simp)) := by
  simpa only [List.nil_append] using actualHistory_refines program input initial rest [] chain initial_refines

theorem runs_prefix_history_refines (program : Program) (input : List Cell) (states : List State) (final : State)
    (run : Runs program input states final) (index : ℕ) (current : State)
    (atState : states[index]?=some current) :
    Refines (actualHistory program (states.take (index+1))) current := by
  have prefixHead : (states.take (index+1)).head?=some initial := by
    simpa only [List.head?_take,Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,ite_false] using run.1
  have prefixLast : (states.take (index+1)).getLast?=some current := by
    simp [List.getLast?_take,atState]
  cases prefixEq : states.take (index+1) with
  | nil => simp only [prefixEq,List.head?_nil,reduceCtorEq] at prefixHead
  | cons first rest =>
    rw [prefixEq] at prefixHead prefixLast
    have same : first=initial:=Option.some.inj prefixHead
    subst first
    have chain : (initial::rest).IsChain (fun a b=>step program input a=some b) := by
      rw [←prefixEq]
      exact run.2.1.take (index+1)
    have refined:=initial_actualHistory_refines program input rest chain
    have lastValue:=List.getLast?_eq_getLast_of_ne_nil (by simp : initial::rest≠[])
    rw [prefixLast] at lastValue
    have endpoint : (initial::rest).getLast (by simp)=current:=(Option.some.inj lastValue).symm
    simpa only [prefixEq,endpoint] using refined

theorem seed_le_foldl_max (values : List ℕ) (seed : ℕ) : seed≤values.foldl max seed := by
  induction values generalizing seed with
  | nil => exact le_refl _
  | cons value rest ih => exact (le_max_left seed value).trans (ih (max seed value))

theorem member_le_foldl_max (values : List ℕ) (seed value : ℕ) (member : value∈values) :
    value≤values.foldl max seed := by
  induction values generalizing seed with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same|later
    · subst value
      exact (le_max_right seed first).trans (seed_le_foldl_max rest (max seed first))
    · exact ih (max seed first) later

theorem state_bits_of_peak (states : List State) (budget : ℕ) (peak : peakOperandBits states≤budget) :
    ∀ current∈states,∀ size∈stateCellBits current,size≤budget := by
  intro current currentMember size sizeMember
  have member : size∈states.flatMap stateCellBits:=List.mem_flatMap.mpr ⟨current,currentMember,sizeMember⟩
  exact (member_le_foldl_max _ 0 size member).trans peak

/-- Every prefix is charged against the SAME whole source time and B.
No history is supplied as a new input, and no per-round B is enlarged. -/
theorem actual_prefix_history_bounds (program : Program) (states : List State) (count budget total : ℕ)
    (peak : peakOperandBits states≤budget) (clock : time program states≤total) :
    (actualHistory program (states.take count)).length≤total ∧
    (∀ event∈actualHistory program (states.take count),(encodeEvent event).length≤4*budget+2) ∧
    (encodeHistory (actualHistory program (states.take count))).length≤total*(4*budget+2) := by
  have prefixBits : ∀ current∈states.take count,∀ size∈stateCellBits current,size≤budget :=
    fun current member=>state_bits_of_peak states budget peak current (List.mem_of_mem_take member)
  have charged:=(time_take_le program states count).trans clock
  exact ⟨(actualHistory_count program _).trans charged,
    actualHistory_event_bounds program _ budget prefixBits,
    (actualHistory_encoded_bound program _ budget prefixBits).trans (Nat.mul_le_mul_right _ charged)⟩

end PDROC.BitVM.VM.BoundaryBudget
