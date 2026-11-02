module
public import Common.ROOT_TM_GCD_ZeroCode_006
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZeroTrace007
open PaperProofs.Common.Native.RationalControllerComputation
open ROOTTMGCDZero006

private theorem commands (relation : Fin 4) (a b : Bool) :
    zeroMachine (aState relation) a = some (flagA relation a, .move .right) ∧
    zeroMachine (flagA relation a) true = some (readB relation a, .move .right) ∧
    zeroMachine (readB relation a) b = some (flagB (update relation a b), .move .right) := by
  fin_cases relation <;> cases a <;> cases b <;> exact ⟨rfl,rfl,rfl⟩

def unitTrace (relation : Fin 4) (a b : Bool) (left right : List Bool) : List (MachineState 27) :=
  [state (aState relation) left (a :: true :: b :: true :: right),
    state (flagA relation a) (a :: left) (true :: b :: true :: right),
    state (readB relation a) (true :: a :: left) (b :: true :: right),
    state (flagB (update relation a b)) (b :: true :: a :: left) (true :: right)]

theorem unit_head (relation : Fin 4) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).head? = some
      (state (aState relation) left (a :: true :: b :: true :: right)) := rfl

theorem unit_last (relation : Fin 4) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).getLast? = some
      (state (flagB (update relation a b)) (b :: true :: a :: left) (true :: right)) := rfl

theorem unit_length (relation : Fin 4) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).length = 4 := rfl

theorem unit_chain (relation : Fin 4) (a b : Bool) (left right : List Bool) :
    (unitTrace relation a b left right).IsChain (fun before after => Turing.TM0.step zeroMachine before = some after) := by
  obtain ⟨h1,h2,h3⟩ := commands relation a b
  simp [unitTrace, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, h1,h2,h3]

theorem unit_advance (relation : Fin 4) (left right : List Bool) :
    Turing.TM0.step zeroMachine (state (flagB relation) left (true :: right)) =
      some (state (aState relation) (true :: left) right) := by
  fin_cases relation <;> simp [Turing.TM0.step, zeroMachine, state, flagB, aState, Turing.Tape.mk₂]

private theorem end_commands (relation : Fin 4) :
    zeroMachine (aState relation) false = some (flagA relation false, .move .right) ∧
    zeroMachine (flagA relation false) false = some (haltLabel relation, .move .left) := by
  fin_cases relation <;> exact ⟨rfl,rfl⟩

def endTrace (relation : Fin 4) (left suffix : List Bool) : List (MachineState 27) :=
  [state (aState relation) left (false :: false :: suffix),
    state (flagA relation false) (false :: left) (false :: suffix),
    state (haltLabel relation) left (false :: false :: suffix)]

theorem end_head (relation : Fin 4) (left suffix : List Bool) :
    (endTrace relation left suffix).head? = some (state (aState relation) left (false :: false :: suffix)) := rfl

theorem end_last (relation : Fin 4) (left suffix : List Bool) :
    (endTrace relation left suffix).getLast? = some (state (haltLabel relation) left (false :: false :: suffix)) := rfl

theorem end_length (relation : Fin 4) (left suffix : List Bool) : (endTrace relation left suffix).length = 3 := rfl

theorem end_chain (relation : Fin 4) (left suffix : List Bool) :
    (endTrace relation left suffix).IsChain (fun before after => Turing.TM0.step zeroMachine before = some after) := by
  obtain ⟨h1,h2⟩ := end_commands relation
  simp [endTrace, List.isChain_cons_cons, Turing.TM0.step, state, Turing.Tape.mk₂, h1,h2]

private theorem append_link (xs ys : List (MachineState 27)) (last first : MachineState 27)
    (hx : xs.IsChain (fun a b => Turing.TM0.step zeroMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step zeroMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step zeroMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step zeroMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def zeroTrace (relation : Fin 4) (context : List Bool) (previous : List (Bool × Bool)) :
    List (Bool × Bool) → List Bool → List (MachineState 27)
  | [], suffix => endTrace relation (leftColumns previous ++ context) suffix
  | (a,b) :: later, suffix =>
    unitTrace relation a b (leftColumns previous ++ context)
      (PSTRTMBinaryAdd024.operandColumns later ++ false :: false :: suffix) ++
      zeroTrace (update relation a b) context ((a,b) :: previous) later suffix

theorem zero_head (relation : Fin 4) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (zeroTrace relation context previous pairs suffix).head? = some
      (state (aState relation) (leftColumns previous ++ context)
        (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix)) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp [zeroTrace, List.head?_append, unit_head, PSTRTMBinaryAdd024.operandColumns]

theorem zero_last (relation : Fin 4) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (zeroTrace relation context previous pairs suffix).getLast? = some
      (state (haltLabel (resultControl relation pairs)) (leftColumns (pairs.reverse ++ previous) ++ context)
        (false :: false :: suffix)) := by
  induction pairs generalizing relation previous with
  | nil => simpa only [zeroTrace, resultControl_nil, List.reverse_nil, List.nil_append] using end_last relation _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp [zeroTrace, List.getLast?_append, ih, resultControl_cons, List.reverse_cons, List.append_assoc]

theorem zero_length (relation : Fin 4) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (zeroTrace relation context previous pairs suffix).length = 4 * pairs.length + 3 := by
  induction pairs generalizing relation previous with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [zeroTrace, List.length_append, unit_length, ih, List.length_cons]
    omega

theorem zero_chain (relation : Fin 4) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (zeroTrace relation context previous pairs suffix).IsChain (fun before after => Turing.TM0.step zeroMachine before = some after) := by
  induction pairs generalizing relation previous with
  | nil => exact end_chain relation _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [zeroTrace]
    apply append_link _ _ _ _ (unit_chain relation a b _ _) (ih (update relation a b) ((a,b) :: previous))
      (unit_last relation a b _ _) (zero_head (update relation a b) context ((a,b) :: previous) later suffix)
    simpa only [leftColumns, PSTRTMCompareCode054.leftColumns, List.flatMap_cons, List.cons_append, List.nil_append] using
      unit_advance (update relation a b) (b :: true :: a :: (leftColumns previous ++ context))
        (PSTRTMBinaryAdd024.operandColumns later ++ false :: false :: suffix)

/-- Whole retained-tape contract: all operands/context and every suffix
cell after the OWN00 are preserved. Computed relation is in actual control. -/
theorem zero_runsFrom (relation : Fin 4) (context : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom zeroMachine
      (state (aState relation) context (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: suffix))
      (zeroTrace relation context [] pairs suffix)
      (state (haltLabel (resultControl relation pairs)) (leftColumns pairs.reverse ++ context) (false :: false :: suffix)) := by
  refine ⟨?_, zero_chain relation context [] pairs suffix, ?_, zero_halt _ _ _⟩
  · simpa only [leftColumns, PSTRTMCompareCode054.leftColumns, List.flatMap_nil, List.nil_append] using zero_head relation context [] pairs suffix
  · simpa only [List.append_nil] using zero_last relation context [] pairs suffix

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDZeroTrace007
