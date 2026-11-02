module
public import Common.PSTR_TM_CompareCode_054
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareTrace055
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompareCode054

private theorem commands (relation : Fin 3) (a b : Bool) :
    compareMachine (aState relation) a = some (flagA relation a, .move .right) ∧
    compareMachine (flagA relation a) true = some (readB relation a, .move .right) ∧
    compareMachine (readB relation a) b = some (flagB (update relation a b), .move .right) := by
  fin_cases relation <;> cases a <;> cases b <;> exact ⟨rfl,rfl,rfl⟩

def unitTrace (relation : Fin 3) (a b : Bool) (left right : List Bool) : List (MachineState 20) :=
  [state (aState relation) left (a :: true :: b :: true :: right),
    state (flagA relation a) (a :: left) (true :: b :: true :: right),
    state (readB relation a) (true :: a :: left) (b :: true :: right),
    state (flagB (update relation a b)) (b :: true :: a :: left) (true :: right)]

theorem unit_head (relation : Fin 3) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).head? = some
      (state (aState relation) left (a :: true :: b :: true :: right)) := rfl

theorem unit_last (relation : Fin 3) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).getLast? = some
      (state (flagB (update relation a b)) (b :: true :: a :: left) (true :: right)) := rfl

theorem unit_length (relation : Fin 3) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).length = 4 := rfl

theorem unit_chain (relation : Fin 3) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).IsChain (fun before after => Turing.TM0.step compareMachine before = some after) := by
  obtain ⟨h1,h2,h3⟩ := commands relation a b
  simp [unitTrace, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, h1,h2,h3]

theorem unit_advance (relation : Fin 3) (left right : List Bool) :
    Turing.TM0.step compareMachine (state (flagB relation) left (true :: right)) =
      some (state (aState relation) (true :: left) right) := by
  fin_cases relation <;> simp [Turing.TM0.step, compareMachine, state, flagB, aState, Turing.Tape.mk₂]

private theorem end_commands (relation : Fin 3) :
    compareMachine (aState relation) false = some (flagA relation false, .move .right) ∧
    compareMachine (flagA relation false) false = some (haltLabel relation, .move .left) := by
  fin_cases relation <;> exact ⟨rfl,rfl⟩

def endTrace (relation : Fin 3) (left suffix : List Bool) : List (MachineState 20) :=
  [state (aState relation) left (false :: false :: suffix),
    state (flagA relation false) (false :: left) (false :: suffix),
    state (haltLabel relation) left (false :: false :: suffix)]

theorem end_head (relation : Fin 3) (left suffix : List Bool) :
    (endTrace relation left suffix).head? = some (state (aState relation) left (false :: false :: suffix)) := rfl

theorem end_last (relation : Fin 3) (left suffix : List Bool) :
    (endTrace relation left suffix).getLast? = some (state (haltLabel relation) left (false :: false :: suffix)) := rfl

theorem end_length (relation : Fin 3) (left suffix : List Bool) : (endTrace relation left suffix).length = 3 := rfl

theorem end_chain (relation : Fin 3) (left suffix : List Bool) :
    (endTrace relation left suffix).IsChain (fun before after => Turing.TM0.step compareMachine before = some after) := by
  obtain ⟨h1,h2⟩ := end_commands relation
  simp [endTrace, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, h1,h2]

private theorem append_link (xs ys : List (MachineState 20)) (last first : MachineState 20)
    (hx : xs.IsChain (fun a b => Turing.TM0.step compareMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step compareMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step compareMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step compareMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def compareTrace (relation : Fin 3) (context : List Bool) (previous : List (Bool × Bool)) :
    List (Bool × Bool) → List Bool → List (MachineState 20)
  | [], suffix => endTrace relation (leftColumns previous ++ context) suffix
  | (a,b) :: later, suffix =>
    unitTrace relation a b (leftColumns previous ++ context)
      (PSTRTMBinaryAdd024.operandColumns later ++ false :: false :: suffix) ++
      compareTrace (update relation a b) context ((a,b) :: previous) later suffix

theorem compare_head (relation : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (compareTrace relation context previous pairs suffix).head? = some
      (state (aState relation) (leftColumns previous ++ context)
        (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix)) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp [compareTrace, List.head?_append, unit_head, PSTRTMBinaryAdd024.operandColumns]

theorem compare_last (relation : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (compareTrace relation context previous pairs suffix).getLast? = some
      (state (haltLabel (resultRelation relation pairs)) (leftColumns (pairs.reverse ++ previous) ++ context)
        (false :: false :: suffix)) := by
  induction pairs generalizing relation previous with
  | nil => simpa only [compareTrace, resultRelation_nil, List.reverse_nil, List.nil_append] using end_last relation _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp [compareTrace, List.getLast?_append, ih, resultRelation_cons, List.reverse_cons, List.append_assoc]

theorem compare_length (relation : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (compareTrace relation context previous pairs suffix).length = 4 * pairs.length + 3 := by
  induction pairs generalizing relation previous with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [compareTrace, List.length_append, unit_length, ih, List.length_cons]
    omega

theorem compare_chain (relation : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (compareTrace relation context previous pairs suffix).IsChain (fun before after => Turing.TM0.step compareMachine before = some after) := by
  induction pairs generalizing relation previous with
  | nil => exact end_chain relation _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [compareTrace]
    apply append_link _ _ _ _ (unit_chain relation a b _ _) (ih (update relation a b) ((a,b) :: previous))
      (unit_last relation a b _ _) (compare_head (update relation a b) context ((a,b) :: previous) later suffix)
    simpa only [leftColumns, List.flatMap_cons, List.cons_append, List.nil_append] using
      unit_advance (update relation a b) (b :: true :: a :: (leftColumns previous ++ context))
        (PSTRTMBinaryAdd024.operandColumns later ++ false :: false :: suffix)

/-- Whole retained-tape contract: all operands/context and every suffix
cell after the OWN00 are preserved. Computed relation is in actual control. -/
theorem compare_runsFrom (relation : Fin 3) (context : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom compareMachine
      (state (aState relation) context (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix))
      (compareTrace relation context [] pairs suffix)
      (state (haltLabel (resultRelation relation pairs)) (leftColumns pairs.reverse ++ context) (false :: false :: suffix)) := by
  refine ⟨?_, compare_chain relation context [] pairs suffix, ?_, compare_halt _ _ _⟩
  · simpa only [leftColumns, List.flatMap_nil, List.nil_append] using compare_head relation context [] pairs suffix
  · simpa only [List.append_nil] using compare_last relation context [] pairs suffix

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareTrace055
