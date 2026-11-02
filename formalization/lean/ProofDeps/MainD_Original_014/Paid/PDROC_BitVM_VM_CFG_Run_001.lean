module

public import Paid.PDROC_BitVM_VM_CFG_Step_003
public import Paid.PDROC_BitVM_VM_Source_RAMTrace_003
public import Paid.PDROC_BitVM_VM_BoundaryBudget_History_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Run

open Turing PaperProofs.Paid.Computation

abbrev Stack := Cleanup.Stack
abbrev Alphabet := Cleanup.Alphabet
abbrev NativeState (Λ σ : Type) := TM2.Cfg Alphabet Λ σ

/-! A boundary is a proof-side actual original prefix. Neither the
original state/event list/prefix/index nor any fuel is in native sigma.
The parent discharges the following local contracts from its real fixed
FullCFG; they are not additional original paper/input qualifications. -/

def Boundary (code : Program) (states : List State) (current : State) (events : List Log.HeapEvent) : Prop :=
  ∃ earlier later : List State, states = earlier ++ current :: later ∧
    events = BoundaryBudget.actualHistory code (earlier ++ [current])

theorem boundary_member (code : Program) (states : List State) (current : State) (events : List Log.HeapEvent)
    (atBoundary : Boundary code states current events) : current ∈ states := by
  obtain ⟨earlier, later, same, history⟩ := atBoundary
  rw [same]
  simp

theorem step_events (code : Program) (current : State) (instruction : Instruction)
    (fetched : code[current.pc]? = some instruction) :
    Log.stepEvents code current = (Log.eventOf instruction current).toList := by
  simp only [Log.stepEvents, fetched, Option.bind_some]

/-- At most one event per ORIGINAL edge, proved from the real event
encoding, not assumed from a replay-equivalent heap interpretation. -/
theorem history_count_edges (code : Program) (first : State) (later : List State) :
    (BoundaryBudget.actualHistory code (first :: later)).length ≤ later.length := by
  induction later generalizing first with
  | nil => simp [BoundaryBudget.actualHistory]
  | cons next rest ih =>
    have event := Log.stepEvents_length code first
    have tail := ih next
    rw [BoundaryBudget.actualHistory_cons_cons, List.length_append]
    simp only [List.length_cons]
    omega

theorem boundary_history_count (code : Program) (earlier : List State) (current : State) :
    (BoundaryBudget.actualHistory code (earlier ++ [current])).length ≤ earlier.length := by
  cases earlier with
  | nil => simp [BoundaryBudget.actualHistory]
  | cons first rest =>
    simpa only [List.cons_append, List.length_append, List.length_singleton, List.length_cons,
      List.length_nil, Nat.zero_add] using
      history_count_edges code first (rest ++ [current])

/-- Prefix history bytes/records are charged against the SAME original
trace's T and B. No per-prefix numerical/history oracle is supplied. -/
theorem boundary_history_bounds (code : Program) (states : List State)
    (current : State) (events : List Log.HeapEvent) (total budget : ℕ)
    (atBoundary : Boundary code states current events)
    (clock : time code states ≤ total) (peak : peakOperandBits states ≤ budget) :
    events.length ≤ total ∧
      (∀ event ∈ events, (Log.encodeEvent event).length ≤ 4 * budget + 2) ∧
      (Log.encodeHistory events).length ≤ total * (4 * budget + 2) := by
  obtain ⟨earlier, later, same, history⟩ := atBoundary
  let segment := earlier ++ [current]
  have decomposition : states = segment ++ later := by
    simpa only [segment, List.append_assoc, List.singleton_append] using same
  have members : ∀ state ∈ segment, state ∈ states := by
    intro state member
    rw [decomposition]
    exact List.mem_append_left _ member
  have bits : ∀ state ∈ segment, ∀ size ∈ stateCellBits state, size ≤ budget :=
    fun state member => BoundaryBudget.state_bits_of_peak states budget peak state (members state member)
  have split := BoundaryBudget.time_append code segment later
  rw [← decomposition] at split
  have charged : time code segment ≤ total := by omega
  rw [history]
  exact ⟨(BoundaryBudget.actualHistory_count code segment).trans charged,
    BoundaryBudget.actualHistory_event_bounds code segment budget bits,
    (BoundaryBudget.actualHistory_encoded_bound code segment budget bits).trans
      (Nat.mul_le_mul_right _ charged)⟩

theorem boundary_next (code : Program) (states : List State) (earlier later : List State)
    (current next : State) (instruction : Instruction)
    (same : states = earlier ++ current :: next :: later)
    (fetched : code[current.pc]? = some instruction) :
    Boundary code states next
      (BoundaryBudget.actualHistory code (earlier ++ [current]) ++ (Log.eventOf instruction current).toList) := by
  refine ⟨earlier ++ [current], later, ?_, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using same
  · have last : (earlier ++ [current]).getLast? = some current :=
      List.getLast?_append_cons earlier current []
    have history := BoundaryBudget.actualHistory_append code (earlier ++ [current]) current next last
    simpa only [step_events code current instruction fetched] using history.symm

end PDROC.BitVM.VM.CFG.Run
