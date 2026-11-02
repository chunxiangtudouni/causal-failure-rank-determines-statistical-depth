module
public import Common.PSTR_TM_CompareFinishCode_057
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareErase058
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompareFinishCode057

private theorem writer_commands (relation : Fin 3) :
    resultMachine (writer relation 0) false = some (writer relation 1, .write true) ∧
    resultMachine (writer relation 1) true = some (writer relation 2, .move .right) ∧
    resultMachine (writer relation 2) false = some (writer relation 3, .write false) ∧
    resultMachine (writer relation 3) false = some (writer relation 4, .move .right) ∧
    resultMachine (writer relation 4) false = some (writer relation 5, .write (PSTRTMCompareValue056.resultLe relation)) ∧
    resultMachine (writer relation 5) (PSTRTMCompareValue056.resultLe relation) = some (51, .move .left) ∧
    resultMachine 51 false = some (52, .move .left) := by
  fin_cases relation <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def writerTrace (relation : Fin 3) : List (MachineState 52) :=
  let bit := PSTRTMCompareValue056.resultLe relation
  [state (writer relation 0) [false] [], state (writer relation 1) [false] [true],
    state (writer relation 2) [true,false] [], state (writer relation 3) [true,false] [false],
    state (writer relation 4) [false,true,false] [], state (writer relation 5) [false,true,false] [bit],
    state 51 [true,false] [false,bit], state 52 [false] [true,false,bit]]

theorem writer_head (relation : Fin 3) :
    (writerTrace relation).head? = some (state (writer relation 0) [false] []) := rfl

theorem writer_last (relation : Fin 3) :
    (writerTrace relation).getLast? = some (state 52 [false] (outputWord relation)) := rfl

theorem writer_length (relation : Fin 3) : (writerTrace relation).length = 8 := rfl

theorem writer_chain (relation : Fin 3) :
    (writerTrace relation).IsChain (fun before after => Turing.TM0.step resultMachine before = some after) := by
  obtain ⟨h1,h2,h3,h4,h5,h6,h7⟩ := writer_commands relation
  simp [writerTrace, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, h1,h2,h3,h4,h5,h6,h7]

private theorem erase_commands (relation : Fin 3) (bit : Bool) :
    resultMachine (eraseFlag relation) true = some (dataLeft relation, .write false) ∧
    resultMachine (dataLeft relation) false = some (eraseData relation, .move .left) ∧
    resultMachine (eraseData relation) bit = some (nextFlag relation, .write false) := by
  fin_cases relation <;> cases bit <;> exact ⟨rfl,rfl,rfl⟩

private theorem next_command (relation : Fin 3) :
    resultMachine (nextFlag relation) false = some (eraseFlag relation, .move .left) := by
  fin_cases relation <;> rfl

private theorem empty_command (relation : Fin 3) :
    resultMachine (eraseFlag relation) false = some (writer relation 0, .move .right) := by
  fin_cases relation <;> rfl

/-- cleared is a ghost count of REAL cells already erased by the trace.
The runtime neither receives nor reads this number. -/
def eraseInitial (relation : Fin 3) : List Bool → Nat → MachineState 52
  | [], cleared => state (eraseFlag relation) [] (List.replicate (cleared + 1) false)
  | bit :: previous, cleared =>
    state (eraseFlag relation) (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: List.replicate cleared false)

def eraseUnit (relation : Fin 3) (bit : Bool) (previous : List Bool) (cleared : Nat) : List (MachineState 52) :=
  [state (eraseFlag relation) (bit :: PSTRTMRawNat010.leftBlocks previous) (true :: List.replicate cleared false),
    state (dataLeft relation) (bit :: PSTRTMRawNat010.leftBlocks previous) (false :: List.replicate cleared false),
    state (eraseData relation) (PSTRTMRawNat010.leftBlocks previous) (bit :: false :: List.replicate cleared false),
    state (nextFlag relation) (PSTRTMRawNat010.leftBlocks previous) (false :: false :: List.replicate cleared false)]

theorem unit_head (relation : Fin 3) (bit : Bool) (previous : List Bool) (cleared : Nat) :
    (eraseUnit relation bit previous cleared).head? = some (eraseInitial relation (bit :: previous) cleared) := rfl

theorem unit_last (relation : Fin 3) (bit : Bool) (previous : List Bool) (cleared : Nat) :
    (eraseUnit relation bit previous cleared).getLast? = some
      (state (nextFlag relation) (PSTRTMRawNat010.leftBlocks previous) (false :: false :: List.replicate cleared false)) := rfl

theorem unit_length (relation : Fin 3) (bit : Bool) (previous : List Bool) (cleared : Nat) :
    (eraseUnit relation bit previous cleared).length = 4 := rfl

theorem unit_chain (relation : Fin 3) (bit : Bool) (previous : List Bool) (cleared : Nat) :
    (eraseUnit relation bit previous cleared).IsChain (fun before after => Turing.TM0.step resultMachine before = some after) := by
  obtain ⟨h1,h2,h3⟩ := erase_commands relation bit
  simp [eraseUnit, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, h1,h2,h3]

theorem unit_advance (relation : Fin 3) (previous : List Bool) (cleared : Nat) :
    Turing.TM0.step resultMachine
      (state (nextFlag relation) (PSTRTMRawNat010.leftBlocks previous) (false :: false :: List.replicate cleared false)) =
      some (eraseInitial relation previous (cleared + 2)) := by
  cases previous <;> simp [eraseInitial, PSTRTMRawNat010.leftBlocks, Turing.TM0.step,
    state, Turing.Tape.mk₂, next_command relation, List.replicate_succ]

theorem empty_advance (relation : Fin 3) (cleared : Nat) :
    Turing.TM0.step resultMachine (eraseInitial relation [] cleared) =
      some (state (writer relation 0) [false] []) := by
  have hb : Turing.ListBlank.mk (List.replicate (cleared + 1) false) = Turing.ListBlank.mk ([] : List Bool) := by
    simpa only [List.nil_append] using PSTRTMPackFinish039.blank_false_suffix [] (cleared + 1)
  have he : eraseInitial relation [] cleared = state (eraseFlag relation) [] [] := by
    simp only [eraseInitial, state, Turing.Tape.mk₂]
    rw [hb]
  rw [he]
  simp [Turing.TM0.step, state, Turing.Tape.mk₂, empty_command relation]

private theorem append_link (xs ys : List (MachineState 52)) (last first : MachineState 52)
    (hx : xs.IsChain (fun a b => Turing.TM0.step resultMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step resultMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step resultMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step resultMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def eraseTrace (relation : Fin 3) : List Bool → Nat → List (MachineState 52)
  | [], cleared => eraseInitial relation [] cleared :: writerTrace relation
  | bit :: previous, cleared => eraseUnit relation bit previous cleared ++ eraseTrace relation previous (cleared + 2)

theorem erase_head (relation : Fin 3) (previous : List Bool) (cleared : Nat) :
    (eraseTrace relation previous cleared).head? = some (eraseInitial relation previous cleared) := by
  cases previous with
  | nil => rfl
  | cons bit previous => simp [eraseTrace, List.head?_append, unit_head]

theorem erase_last (relation : Fin 3) (previous : List Bool) (cleared : Nat) :
    (eraseTrace relation previous cleared).getLast? = some (state 52 [false] (outputWord relation)) := by
  induction previous generalizing cleared with
  | nil => rfl
  | cons bit previous ih => simp only [eraseTrace, List.getLast?_append, ih, Option.some_or]

theorem erase_length (relation : Fin 3) (previous : List Bool) (cleared : Nat) :
    (eraseTrace relation previous cleared).length = 4 * previous.length + 9 := by
  induction previous generalizing cleared with
  | nil => rfl
  | cons bit previous ih =>
    simp only [eraseTrace, List.length_append, unit_length, ih, List.length_cons]
    omega

theorem erase_chain (relation : Fin 3) (previous : List Bool) (cleared : Nat) :
    (eraseTrace relation previous cleared).IsChain (fun before after => Turing.TM0.step resultMachine before = some after) := by
  induction previous generalizing cleared with
  | nil =>
    rw [eraseTrace]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      simp only [writer_head, Option.mem_some_iff] at ha
      subst after
      exact empty_advance relation cleared
    · exact writer_chain relation
  | cons bit previous ih =>
    rw [eraseTrace]
    exact append_link _ _ _ _ (unit_chain relation bit previous cleared) (ih (cleared + 2))
      (unit_last relation bit previous cleared) (erase_head relation previous (cleared + 2))
      (unit_advance relation previous cleared)

theorem output_tape (relation : Fin 3) :
    (state 52 [false] (outputWord relation)).Tape = Turing.Tape.mk₁ (outputWord relation) := by
  simp only [state, Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareErase058
