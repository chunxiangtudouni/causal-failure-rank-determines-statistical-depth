module

public import Paid.PDROC_BitVM_Log_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Source-history size from the actual source chain and its actual operand
bound. No assumption asks the caller to provide a bounded arbitrary log. This
is still source representation mathematics, not Boolean lookup code. -/

namespace PDROC.BitVM.Log

open PaperProofs.Paid.Computation

theorem stepEvents_bounded (program : Array Instruction) (before : State) (budget : ℕ)
    (allBits : ∀ size ∈ stateCellBits before, size ≤ budget) :
    ∀ event ∈ stepEvents program before, (encodeEvent event).length ≤ 4 * budget + 2 := by
  intro event member
  cases fetched : program[before.pc]? with
  | none => simp [stepEvents, fetched] at member
  | some instruction =>
    have actual : eventOf instruction before = some event := by
      simpa [stepEvents, fetched] using member
    exact actual_event_length instruction before event budget allBits actual

theorem stepEvents_cost (program : Array Instruction) (before : State) :
    (stepEvents program before).length ≤
      (((program[before.pc]?).map Instruction.primitives).getD []).length := by
  cases fetched : program[before.pc]? with
  | none => simp [stepEvents, fetched]
  | some instruction =>
    have one := stepEvents_length program before
    simp only [Option.map_some, Option.getD_some, Instruction.primitives,
      List.length_append, List.length_replicate, List.length_cons, List.length_nil]
    omega

theorem chain_history_bounded (program : Array Instruction) (input : List Cell)
    (before : State) (rest : List State) (events : List HeapEvent) (budget : ℕ)
    (chain : (before :: rest).IsChain (fun a b => step program input a = some b))
    (refines : Refines events before)
    (allBits : ∀ current ∈ before :: rest, ∀ size ∈ stateCellBits current, size ≤ budget)
    (eventBounds : ∀ event ∈ events, (encodeEvent event).length ≤ 4 * budget + 2) :
    ∃ finalEvents, Refines finalEvents ((before :: rest).getLast (by simp)) ∧
      finalEvents.length ≤ events.length + rest.length ∧
      finalEvents.length ≤ events.length + time program (before :: rest) ∧
      ∀ event ∈ finalEvents, (encodeEvent event).length ≤ 4 * budget + 2 := by
  induction rest generalizing before events with
  | nil => exact ⟨events, refines, by simp, Nat.le_add_right _ _, eventBounds⟩
  | cons middle rest ih =>
    have first := (List.isChain_cons_cons.mp chain).1
    have newBounds := stepEvents_bounded program before budget
      (allBits before (by simp))
    have joinedBounds : ∀ event ∈ events ++ stepEvents program before,
        (encodeEvent event).length ≤ 4 * budget + 2 := by
      intro event member
      rcases List.mem_append.mp member with old | new
      · exact eventBounds event old
      · exact newBounds event new
    obtain ⟨finalEvents, finalRefines, size, timeSize, finalBounds⟩ := ih middle
      (events ++ stepEvents program before) chain.tail
      (step_refines program input events before middle refines first)
      (by intro current member; exact allBits current (List.mem_cons_of_mem before member))
      joinedBounds
    refine ⟨finalEvents, ?_, ?_, ?_, finalBounds⟩
    · simpa only [List.getLast_cons_cons] using finalRefines
    · have one := stepEvents_length program before
      simp only [List.length_append] at size
      simp only [List.length_cons]
      omega
    · have one := stepEvents_cost program before
      simp only [List.length_append] at timeSize
      simp only [time, primitiveTrace, List.flatMap_cons, List.length_append] at timeSize ⊢
      omega

/-- Exact source heap/live and its encoded byte count from one actual chain.
`rest.length` is its number of successful source transitions. -/
theorem initial_chain_encoded_history (program : Array Instruction) (input : List Cell)
    (rest : List State) (budget : ℕ)
    (chain : (initial :: rest).IsChain (fun a b => step program input a = some b))
    (allBits : ∀ current ∈ initial :: rest, ∀ size ∈ stateCellBits current, size ≤ budget) :
    ∃ events, Refines events ((initial :: rest).getLast (by simp)) ∧
      events.length ≤ rest.length ∧
      events.length ≤ time program (initial :: rest) ∧
      (encodeHistory events).length ≤ time program (initial :: rest) * (4 * budget + 2) := by
  obtain ⟨events, refines, size, timeSize, bounds⟩ := chain_history_bounded
    program input initial rest [] budget chain initial_refines allBits (by simp)
  simp only [List.length_nil, zero_add] at size timeSize
  refine ⟨events, refines, size, timeSize, ?_⟩
  exact (encodeHistory_length events budget bounds).trans (Nat.mul_le_mul_right _ timeSize)

end PDROC.BitVM.Log
