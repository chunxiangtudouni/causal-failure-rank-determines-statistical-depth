module
public import Structure.PA17_TM_Division_Sub_001a

/-! A real single-pass Bool TM0 trace. All B bits, true flags, arbitrary
left context, owned00 cells and arbitrary following suffix are retained. -/
@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionSub001
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def unitTrace (borrow a b : Bool) (left right : List Bool) : List (MachineState 27) :=
  let d := differenceBit borrow a b
  let c := borrowBit borrow a b
  [state (readA borrow) left (a :: true :: b :: true :: right),
    state (flagA borrow a) (a :: left) (true :: b :: true :: right),
    state (readB borrow a) (true :: a :: left) (b :: true :: right),
    state (backFlag d c) (a :: left) (true :: b :: true :: right),
    state (writeA d c) left (a :: true :: b :: true :: right),
    state (advance 0 c) left (d :: true :: b :: true :: right),
    state (advance 1 c) (d :: left) (true :: b :: true :: right),
    state (advance 2 c) (true :: d :: left) (b :: true :: right),
    state (advance 3 c) (b :: true :: d :: left) (true :: right)]

theorem unit_head (borrow a b : Bool) (left right : List Bool) :
    (unitTrace borrow a b left right).head? = some
      (state (readA borrow) left (a :: true :: b :: true :: right)) := rfl

theorem unit_last (borrow a b : Bool) (left right : List Bool) :
    (unitTrace borrow a b left right).getLast? = some
      (state (advance 3 (borrowBit borrow a b)) (b :: true :: differenceBit borrow a b :: left) (true :: right)) := rfl

theorem unit_length (borrow a b : Bool) (left right : List Bool) :
    (unitTrace borrow a b left right).length = 9 := rfl

theorem unit_chain (borrow a b : Bool) (left right : List Bool) :
    (unitTrace borrow a b left right).IsChain
      (fun before after => Turing.TM0.step subMachine before = some after) := by
  cases borrow <;> cases a <;> cases b <;>
    simp [unitTrace, List.isChain_cons_cons, Turing.TM0.step, subMachine, state,
      readA, flagA, readB, backFlag, writeA, advance, differenceBit, borrowBit, Turing.Tape.mk₂]

theorem unit_advance (borrow : Bool) (left right : List Bool) :
    Turing.TM0.step subMachine (state (advance 3 borrow) left (true :: right)) =
      some (state (readA borrow) (true :: left) right) := by
  cases borrow <;> simp [Turing.TM0.step, subMachine, state, readA, advance, Turing.Tape.mk₂]

def endTrace (borrow : Bool) (left suffix : List Bool) : List (MachineState 27) :=
  [state (readA borrow) left (false :: false :: suffix),
    state (flagA borrow false) (false :: left) (false :: suffix),
    state (haltLabel borrow) left (false :: false :: suffix)]

theorem end_head (borrow : Bool) (left suffix : List Bool) :
    (endTrace borrow left suffix).head? = some (state (readA borrow) left (false :: false :: suffix)) := rfl

theorem end_last (borrow : Bool) (left suffix : List Bool) :
    (endTrace borrow left suffix).getLast? = some (state (haltLabel borrow) left (false :: false :: suffix)) := rfl

theorem end_length (borrow : Bool) (left suffix : List Bool) : (endTrace borrow left suffix).length = 3 := rfl

theorem end_chain (borrow : Bool) (left suffix : List Bool) :
    (endTrace borrow left suffix).IsChain (fun before after => Turing.TM0.step subMachine before = some after) := by
  cases borrow <;> simp [endTrace, List.isChain_cons_cons, Turing.TM0.step, subMachine,
    state, readA, flagA, haltLabel, Turing.Tape.mk₂]

def subTrace (borrow : Bool) (context : List Bool) (previous : List (Bool × Bool)) :
    List (Bool × Bool) → List Bool → List (MachineState 27)
  | [], suffix => endTrace borrow (leftColumns previous ++ context) suffix
  | (a,b) :: later, suffix =>
    unitTrace borrow a b (leftColumns previous ++ context)
      (operandColumns later ++ false :: false :: suffix) ++
      subTrace (borrowBit borrow a b) context ((differenceBit borrow a b,b) :: previous) later suffix

theorem sub_head (borrow : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (subTrace borrow context previous pairs suffix).head? = some
      (state (readA borrow) (leftColumns previous ++ context) (operandColumns pairs ++ false :: false :: suffix)) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp [subTrace, List.head?_append, unit_head, operandColumns]

theorem sub_last (borrow : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (subTrace borrow context previous pairs suffix).getLast? = some
      (state (haltLabel (finalBorrow borrow pairs))
        (leftColumns ((subPairs borrow pairs).reverse ++ previous) ++ context) (false :: false :: suffix)) := by
  induction pairs generalizing borrow previous with
  | nil => simpa only [subTrace, subPairs, finalBorrow, List.reverse_nil, List.nil_append] using end_last borrow _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp [subTrace, List.getLast?_append, ih, subPairs, finalBorrow, List.reverse_cons, List.append_assoc]

theorem sub_length (borrow : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (subTrace borrow context previous pairs suffix).length = 9 * pairs.length + 3 := by
  induction pairs generalizing borrow previous with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [subTrace, List.length_append, unit_length, ih, List.length_cons]
    omega

theorem sub_chain (borrow : Bool) (context : List Bool) (previous pairs : List (Bool × Bool)) (suffix : List Bool) :
    (subTrace borrow context previous pairs suffix).IsChain
      (fun before after => Turing.TM0.step subMachine before = some after) := by
  induction pairs generalizing borrow previous with
  | nil => exact end_chain borrow _ suffix
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [subTrace]
    apply (unit_chain borrow a b _ _).append
      (ih (borrowBit borrow a b) ((differenceBit borrow a b,b) :: previous))
    intro before hb after ha
    simp only [unit_last, Option.mem_some_iff] at hb
    simp only [sub_head, Option.mem_some_iff] at ha
    subst before
    subst after
    simpa only [leftColumns, List.flatMap_cons, List.cons_append, List.nil_append] using
      unit_advance (borrowBit borrow a b) (b :: true :: differenceBit borrow a b :: (leftColumns previous ++ context))
        (operandColumns later ++ false :: false :: suffix)

/-- Unconditional genuine trace for every bit list and incoming borrow.
Its actual halt control retains the computed borrow and its whole tape
retains B, all flags, both OWN00 cells, all context and all suffix cells. -/
theorem sub_runsFrom (borrow : Bool) (context : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom subMachine
      (state (readA borrow) context (operandColumns pairs ++ false :: false :: suffix))
      (subTrace borrow context [] pairs suffix)
      (state (haltLabel (finalBorrow borrow pairs))
        (leftColumns (subPairs borrow pairs).reverse ++ context) (false :: false :: suffix)) := by
  refine ⟨?_, sub_chain borrow context [] pairs suffix, ?_, sub_halt _ _ _⟩
  · simpa only [leftColumns, List.flatMap_nil, List.nil_append] using sub_head borrow context [] pairs suffix
  · simpa only [List.append_nil] using sub_last borrow context [] pairs suffix

theorem sub_visitedSpace_le (borrow : Bool) (context : List Bool) (pairs : List (Bool × Bool))
    (suffix : List Bool) (inputLength : Nat) :
    visitedSpace subMachine inputLength (subTrace borrow context [] pairs suffix) ≤ inputLength + 18 * pairs.length + 7 := by
  have hs := PSTRTMTrace002.visitedSpace_le subMachine inputLength (subTrace borrow context [] pairs suffix)
  rw [sub_length] at hs
  omega

theorem sub_eval (borrow : Bool) (context : List Bool) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    state (haltLabel (finalBorrow borrow pairs))
        (leftColumns (subPairs borrow pairs).reverse ++ context) (false :: false :: suffix) ∈
      StateTransition.eval (Turing.TM0.step subMachine)
        (state (readA borrow) context (operandColumns pairs ++ false :: false :: suffix)) := by
  have h := sub_runsFrom borrow context pairs suffix
  exact StateTransition.mem_eval.mpr ⟨PSTRTMTrace002.chain_reaches _ _ _ _ h.1 h.2.1 h.2.2.1, h.2.2.2⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionSub001
