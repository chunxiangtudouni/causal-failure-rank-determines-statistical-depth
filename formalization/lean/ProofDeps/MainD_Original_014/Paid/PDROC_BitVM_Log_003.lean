module

public import Paid.PDROC_BitVM_Log_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Record-size specification over the official self-delimiting codec. These
length calculations do not implement encoding or lookup on a Turing machine. -/

namespace PDROC.BitVM.Log

open PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

def encodeEvent (event : HeapEvent) : List Bool :=
  match event.value with
  | none => false :: encodeNatBits event.address
  | some value => true :: (encodeNatBits event.address ++ encodeCellBits value)

/-- Newest record is physically first, with each record in ordinary bit order. -/
def encodeHistory (events : List HeapEvent) : List Bool :=
  events.reverse.flatMap encodeEvent

theorem encodeHistory_append (events : List HeapEvent) (event : HeapEvent) :
    encodeHistory (events ++ [event]) = encodeEvent event ++ encodeHistory events := by
  simp [encodeHistory, List.reverse_append]

theorem nat_word_length (value : ℕ) :
    (encodeNatBits value).length = 2 * natBits value + 1 := by
  simp only [encodeNatBits, List.length_append, List.length_replicate,
    List.length_cons, List.length_nil, List.length_ofFn]
  omega

theorem cell_word_length (cell : Cell) :
    (encodeCellBits cell).length ≤ 2 * cell.bits := by
  cases cell with
  | natural value =>
    simp only [encodeCellBits, List.length_cons, nat_word_length, Cell.bits]
    omega
  | rational value =>
    simp only [encodeCellBits, List.length_append, List.length_cons, List.length_nil,
      nat_word_length, Cell.bits, ratEncodingBits, ratNumBits, ratDenBits]
    omega

theorem encodeEvent_length (event : HeapEvent) (budget : ℕ)
    (address : natBits event.address ≤ budget)
    (payload : ∀ value ∈ event.value, value.bits ≤ budget) :
    (encodeEvent event).length ≤ 4 * budget + 2 := by
  cases value : event.value with
  | none => simp only [encodeEvent, value, List.length_cons, nat_word_length]; omega
  | some cell =>
    have bound := payload cell (by simp [value])
    have encoded := cell_word_length cell
    simp only [encodeEvent, value, List.length_cons, List.length_append, nat_word_length]
    omega

theorem register_bits (before : State) (budget : ℕ)
    (allBits : ∀ size ∈ stateCellBits before, size ≤ budget) (register : Register) :
    (before.register register).bits ≤ budget := by
  apply allBits
  simp only [stateCellBits, List.mem_append]
  apply Or.inl
  apply Or.inl
  apply Or.inl
  apply List.mem_map.mpr
  refine ⟨register, ?_, rfl⟩
  cases register <;> simp [registers]

theorem register_address_bits (before : State) (budget : ℕ)
    (allBits : ∀ size ∈ stateCellBits before, size ≤ budget)
    (pointer : Register) (address : ℕ)
    (typed : (before.register pointer).nat? = some address) : natBits address ≤ budget := by
  have bound := register_bits before budget allBits pointer
  cases value : before.register pointer with
  | natural number =>
    simp only [value, Cell.nat?, Option.some.injEq] at typed
    subst number
    simp only [value, Cell.bits] at bound
    omega
  | rational number => simp only [value, Cell.nat?, reduceCtorEq] at typed

theorem actual_event_length (instruction : Instruction) (before : State)
    (event : HeapEvent) (budget : ℕ)
    (allBits : ∀ size ∈ stateCellBits before, size ≤ budget)
    (actual : eventOf instruction before = some event) :
    (encodeEvent event).length ≤ 4 * budget + 2 := by
  cases instruction with
  | store pointer source =>
    cases typed : (before.register pointer).nat? with
    | none => simp [eventOf, typed] at actual
    | some address =>
      simp only [eventOf, typed, Option.map_some, Option.some.injEq] at actual
      subst event
      apply encodeEvent_length
      · exact register_address_bits before budget allBits pointer address typed
      · intro value member
        have equal : value = before.register source := (Option.mem_some_iff.mp member).symm
        subst value
        exact register_bits before budget allBits source
  | release pointer =>
    cases typed : (before.register pointer).nat? with
    | none => simp [eventOf, typed] at actual
    | some address =>
      simp only [eventOf, typed, Option.map_some, Option.some.injEq] at actual
      subst event
      apply encodeEvent_length
      · exact register_address_bits before budget allBits pointer address typed
      · simp
  | constant target value | move target source | loadInput target pointer
  | load target pointer | natOp operation target left right
  | ratOp operation target left right | natCompare comparison target left right
  | ratCompare comparison target left right | natToRat target source
  | numeratorAbs target source | denominator target source | negative target source
  | branchZero test yes no | jump destination | jumpIndirect source | output source
  | halt => simp [eventOf] at actual

theorem encodeHistory_length (events : List HeapEvent) (budget : ℕ)
    (bounded : ∀ event ∈ events, (encodeEvent event).length ≤ 4 * budget + 2) :
    (encodeHistory events).length ≤ events.length * (4 * budget + 2) := by
  suffices generic : ∀ history : List HeapEvent,
      (∀ event ∈ history, (encodeEvent event).length ≤ 4 * budget + 2) →
      (history.flatMap encodeEvent).length ≤ history.length * (4 * budget + 2) by
    simpa only [encodeHistory, List.length_reverse] using generic events.reverse
      (by simpa only [List.mem_reverse] using bounded)
  intro history
  induction history with
  | nil => simp
  | cons event history ih =>
    intro bounds
    have first := bounds event (by simp)
    have rest := ih (by intro item member; exact bounds item (by simp [member]))
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    nlinarith

end PDROC.BitVM.Log
