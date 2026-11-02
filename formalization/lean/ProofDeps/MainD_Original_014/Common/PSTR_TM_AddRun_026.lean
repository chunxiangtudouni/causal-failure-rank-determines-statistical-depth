module
public import Common.PSTR_TM_AddTrace_025
public import Common.PSTR_TM_RawNat_010

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAddRun026
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMBinaryAdd024 PSTRTMAddTrace025 PSTRTMTrace002

private theorem append_link (xs ys : List (MachineState 49)) (last first : MachineState 49)
    (hx : xs.IsChain (fun a b => Turing.TM0.step addMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step addMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step addMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step addMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def rewindAll (previous : List Bool) : List (MachineState 49) :=
  state 36 (leftResults previous) [false] :: rewindTrace previous [false]

theorem rewindAll_head (previous : List Bool) :
    (rewindAll previous).head? = some (state 36 (leftResults previous) [false]) := rfl

theorem rewindAll_length (previous : List Bool) :
    (rewindAll previous).length = 4 * previous.length + 3 := by
  simp only [rewindAll, List.length_cons, rewind_length]

theorem rewindAll_last (previous : List Bool) :
    (rewindAll previous).getLast? = some
      (state 43 [false] (resultColumns previous.reverse ++ [false])) := by
  have hne : rewindTrace previous [false] ≠ [] := by
    have hh := rewind_head previous [false]
    intro h
    simp [h] at hh
  rw [rewindAll, List.getLast?_cons_of_ne_nil hne, rewind_last]

theorem rewindAll_chain (previous : List Bool) :
    (rewindAll previous).IsChain (fun a b => Turing.TM0.step addMachine a = some b) := by
  apply List.isChain_cons.mpr
  constructor
  · intro next hn
    rw [rewind_head] at hn
    have he := Option.mem_some_iff.mp hn
    subst next
    cases previous <;>
      simp [rewindInitial, Turing.TM0.step, addMachine, state, leftResults, Turing.Tape.mk₂]
  · exact rewind_chain previous [false]

/-- The carry extension writes all FOUR actual owned cells, then invokes
the same real rewind. The no-carry branch does not extend the result. -/
def endTrace (carry : Bool) (previous : List Bool) : List (MachineState 49) :=
  let left := leftResults previous
  if carry then
    [state 1 left [], state (flagState true false) (false :: left) [],
      state 41 left [false], state 42 left [true], state 44 (true :: left) [],
      state 45 (true :: left) [true], state 46 (true :: true :: left) [],
      state 47 (true :: true :: left) [false], state 48 (false :: true :: true :: left) [],
      state 49 (false :: true :: true :: left) [true]] ++ rewindAll (true :: previous)
  else [state 0 left [], state (flagState false false) (false :: left) []] ++ rewindAll previous

theorem end_head (carry : Bool) (previous : List Bool) :
    (endTrace carry previous).head? = some (state (carryState carry) (leftResults previous) []) := by
  cases carry <;> rfl

theorem end_length_le (carry : Bool) (previous : List Bool) :
    (endTrace carry previous).length ≤ 4 * previous.length + 17 := by
  cases carry <;> simp only [endTrace, Bool.false_eq_true, ite_false, ite_true,
    List.length_append, List.length_cons, List.length_nil, rewindAll_length] <;> omega

theorem end_last (carry : Bool) (previous : List Bool) :
    (endTrace carry previous).getLast? = some
      (state 43 [false] (resultColumns (previous.reverse ++ sumDigits carry []) ++ [false])) := by
  cases carry with
  | false =>
    dsimp only [endTrace]
    rw [ite_eq_right Bool.false_ne_true]
    rw [List.getLast?_append, rewindAll_last]
    simp [sumDigits]
  | true =>
    dsimp only [endTrace]
    rw [ite_eq_left (rfl : (true : Bool) = true)]
    rw [List.getLast?_append, rewindAll_last]
    simp [sumDigits, List.reverse_cons]

theorem end_chain (carry : Bool) (previous : List Bool) :
    (endTrace carry previous).IsChain (fun a b => Turing.TM0.step addMachine a = some b) := by
  cases carry with
  | false =>
    simp only [endTrace, Bool.false_eq_true, ite_false, List.cons_append, List.nil_append,
      List.isChain_cons_cons]
    constructor
    · simp [Turing.TM0.step, addMachine, state, flagState, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [rewindAll_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step, addMachine, state, flagState, Turing.Tape.mk₂,
        PSTRTMRawNat010.blank_single_false]
    · exact rewindAll_chain previous
  | true =>
    let left := leftResults previous
    let segment := [state 1 left [], state (flagState true false) (false :: left) [],
      state 41 left [false], state 42 left [true], state 44 (true :: left) [],
      state 45 (true :: left) [true], state 46 (true :: true :: left) [],
      state 47 (true :: true :: left) [false], state 48 (false :: true :: true :: left) [],
      state 49 (false :: true :: true :: left) [true]]
    have hc : segment.IsChain (fun a b => Turing.TM0.step addMachine a = some b) := by
      simp [segment, List.isChain_cons_cons, Turing.TM0.step, addMachine, state,
        flagState, Turing.Tape.mk₂, PSTRTMRawNat010.blank_single_false]
    apply append_link segment (rewindAll (true :: previous)) _ _ hc (rewindAll_chain _)
      (by rfl) (rewindAll_head _)
    simp [Turing.TM0.step, addMachine, state, leftResults, Turing.Tape.mk₂,
      PSTRTMRawNat010.blank_single_false, left]

def addTrace (carry : Bool) (previous : List Bool) : List (Bool × Bool) → List (MachineState 49)
  | [] => endTrace carry previous
  | (a,b) :: later => columnTrace carry a b previous later ++
      addTrace (carryBit carry a b) (sumBit carry a b :: previous) later

theorem add_head (carry : Bool) (previous : List Bool) (pairs : List (Bool × Bool)) :
    (addTrace carry previous pairs).head? = some
      (state (carryState carry) (leftResults previous) (operandColumns pairs)) := by
  cases pairs with
  | nil => exact end_head carry previous
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp [addTrace, List.head?_append, column_head]

theorem add_length_le (carry : Bool) (previous : List Bool) (pairs : List (Bool × Bool)) :
    (addTrace carry previous pairs).length ≤ 14 * pairs.length + 4 * previous.length + 17 := by
  induction pairs generalizing carry previous with
  | nil => simpa [addTrace] using end_length_le carry previous
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    have h := ih (carryBit carry a b) (sumBit carry a b :: previous)
    simp only [addTrace, List.length_append, column_length, List.length_cons] at h ⊢
    omega

theorem add_last (carry : Bool) (previous : List Bool) (pairs : List (Bool × Bool)) :
    (addTrace carry previous pairs).getLast? = some
      (state 43 [false] (resultColumns (previous.reverse ++ sumDigits carry pairs) ++ [false])) := by
  induction pairs generalizing carry previous with
  | nil => exact end_last carry previous
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp [addTrace, List.getLast?_append, ih, List.reverse_cons, sumDigits, List.append_assoc]

theorem add_chain (carry : Bool) (previous : List Bool) (pairs : List (Bool × Bool)) :
    (addTrace carry previous pairs).IsChain (fun a b => Turing.TM0.step addMachine a = some b) := by
  induction pairs generalizing carry previous with
  | nil => exact end_chain carry previous
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [addTrace]
    exact append_link _ _ _ _ (column_chain carry a b previous later)
      (ih (carryBit carry a b) (sumBit carry a b :: previous))
      (column_last carry a b previous later)
      (add_head (carryBit carry a b) (sumBit carry a b :: previous) later)
      (column_advance carry a b previous later)

theorem add_runs (pairs : List (Bool × Bool)) :
    Runs addMachine (operandColumns pairs) (addTrace false [] pairs)
      (state 43 [false] (resultColumns (sumDigits false pairs) ++ [false])) := by
  apply runs_of_chain
  · simpa [Turing.TM0.init, Turing.Tape.mk₁, state, carryState, leftResults] using add_head false [] pairs
  · exact add_chain false [] pairs
  · simpa using add_last false [] pairs
  · exact add_halt _ _

/-- A substantive binary addition kernel on actual aligned bit columns.
Original two-field raw transport and canonical output remain separate work;
this format is NOT silently assumed by original B23. -/
theorem add_computes (pairs : List (Bool × Bool)) :
    computes addMachine (operandColumns pairs) (resultColumns (sumDigits false pairs))
      (14 * pairs.length + 17) (32 * pairs.length + 35) := by
  refine ⟨addTrace false [] pairs,
    state 43 [false] (resultColumns (sumDigits false pairs) ++ [false]), add_runs pairs, ?_, ?_, ?_⟩
  · simpa [state, Turing.Tape.mk₂] using
      PSTRTMRawNat010.blank_append_false (resultColumns (sumDigits false pairs))
  · simpa using add_length_le false [] pairs
  · have hs := visitedSpace_le addMachine (operandColumns pairs).length (addTrace false [] pairs)
    have ht := add_length_le false [] pairs
    rw [operandColumns_length] at hs ⊢
    simp only [List.length_nil] at ht
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAddRun026
