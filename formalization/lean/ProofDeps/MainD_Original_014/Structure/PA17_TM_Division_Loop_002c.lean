module

public import Structure.PA17_TM_Division_Loop_002b

/-! Every rightward archive-return move is real. The two true flags in
each four-cell archive column distinguish its payload from the actual
three-false separator, whose last cell is crossed before halting at firstR. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002

open PSTRTMCompareCode054 PSTRTMBinaryAdd024

def returnUnitTrace (mode : Fin 3) (a b : Bool) (left right : List Bool) : List (MachineState 27) :=
  [sourceState (returnSource mode) left (a :: true :: b :: true :: right),
   sourceState (returnFlagA mode) (a :: left) (true :: b :: true :: right),
   sourceState (returnPending mode) (true :: a :: left) (b :: true :: right),
   sourceState (returnFlagB mode) (b :: true :: a :: left) (true :: right)]

theorem return_unit_head (mode : Fin 3) (a b : Bool) (left right : List Bool) :
    (returnUnitTrace mode a b left right).head? = some
      (sourceState (returnSource mode) left (a :: true :: b :: true :: right)) := rfl

theorem return_unit_last (mode : Fin 3) (a b : Bool) (left right : List Bool) :
    (returnUnitTrace mode a b left right).getLast? = some
      (sourceState (returnFlagB mode) (b :: true :: a :: left) (true :: right)) := rfl

theorem return_unit_length (mode : Fin 3) (a b : Bool) (left right : List Bool) :
    (returnUnitTrace mode a b left right).length = 4 := rfl

theorem return_unit_chain (mode : Fin 3) (a b : Bool) (left right : List Bool) :
    (returnUnitTrace mode a b left right).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  obtain ⟨h1, h2, h3, _⟩ := return_commands mode a b
  simp [returnUnitTrace, List.isChain_cons_cons, Turing.TM0.step, sourceState, Turing.Tape.mk₂, h1, h2, h3]

theorem return_unit_advance (mode : Fin 3) (left right : List Bool) :
    Turing.TM0.step sourceMachine (sourceState (returnFlagB mode) left (true :: right)) =
      some (sourceState (returnSource mode) (true :: left) right) := by
  have command := (return_commands mode false false).2.2.2
  simp [Turing.TM0.step, sourceState, Turing.Tape.mk₂, command]

def returnEndTrace (mode : Fin 3) (left resident : List Bool) : List (MachineState 27) :=
  [sourceState (returnSource mode) left (false :: false :: false :: resident),
   sourceState (returnFlagA mode) (false :: left) (false :: false :: resident),
   sourceState (returnHop mode) (false :: false :: left) (false :: resident),
   sourceState (sourceHalt mode) (false :: false :: false :: left) resident]

theorem return_end_head (mode : Fin 3) (left resident : List Bool) :
    (returnEndTrace mode left resident).head? = some
      (sourceState (returnSource mode) left (false :: false :: false :: resident)) := rfl

theorem return_end_last (mode : Fin 3) (left resident : List Bool) :
    (returnEndTrace mode left resident).getLast? = some
      (sourceState (sourceHalt mode) (false :: false :: false :: left) resident) := rfl

theorem return_end_length (mode : Fin 3) (left resident : List Bool) :
    (returnEndTrace mode left resident).length = 4 := rfl

theorem return_end_chain (mode : Fin 3) (left resident : List Bool) :
    (returnEndTrace mode left resident).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  obtain ⟨h1, h2, h3⟩ := return_end_commands mode
  simp [returnEndTrace, List.isChain_cons_cons, Turing.TM0.step, sourceState, Turing.Tape.mk₂, h1, h2, h3]

def returnTrace (mode : Fin 3) (context : List Bool) (previous : List (Bool × Bool)) :
    List (Bool × Bool) → List Bool → List (MachineState 27)
  | [], resident => returnEndTrace mode (leftColumns previous ++ context) resident
  | (a,b) :: later, resident =>
    returnUnitTrace mode a b (leftColumns previous ++ context)
      (operandColumns later ++ false :: false :: false :: resident) ++
    returnTrace mode context ((a,b) :: previous) later resident

theorem return_head (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (returnTrace mode context previous pairs resident).head? = some
      (sourceState (returnSource mode) (leftColumns previous ++ context)
        (operandColumns pairs ++ false :: false :: false :: resident)) := by
  cases pairs with
  | nil => rfl
  | cons pair later =>
    obtain ⟨a,b⟩ := pair
    simp [returnTrace, List.head?_append, return_unit_head, operandColumns]

theorem return_last (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (returnTrace mode context previous pairs resident).getLast? = some
      (sourceState (sourceHalt mode) (false :: false :: false :: (leftColumns (pairs.reverse ++ previous) ++ context)) resident) := by
  induction pairs generalizing previous with
  | nil => simpa only [returnTrace, List.reverse_nil, List.nil_append] using return_end_last mode _ resident
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp [returnTrace, List.getLast?_append, ih, List.reverse_cons, List.append_assoc]

theorem return_length (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (returnTrace mode context previous pairs resident).length = 4 * pairs.length + 4 := by
  induction pairs generalizing previous with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [returnTrace, List.length_append, return_unit_length, ih, List.length_cons]
    omega

theorem return_chain (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (returnTrace mode context previous pairs resident).IsChain (fun before after => Turing.TM0.step sourceMachine before = some after) := by
  induction pairs generalizing previous with
  | nil => exact return_end_chain mode _ resident
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [returnTrace]
    apply (return_unit_chain mode a b _ _).append (ih ((a,b) :: previous))
    intro before hb after ha
    simp only [return_unit_last, Option.mem_some_iff] at hb
    simp only [return_head, Option.mem_some_iff] at ha
    subst before
    subst after
    simpa only [leftColumns, List.flatMap_cons, List.cons_append, List.nil_append] using
      return_unit_advance mode (b :: true :: a :: (leftColumns previous ++ context))
        (operandColumns later ++ false :: false :: false :: resident)

theorem return_runsFrom (mode : Fin 3) (context : List Bool) (pairs : List (Bool × Bool)) (resident : List Bool) :
    PSTRTMSeq005.RunsFrom sourceMachine
      (sourceState (returnSource mode) context (operandColumns pairs ++ false :: false :: false :: resident))
      (returnTrace mode context [] pairs resident)
      (sourceState (sourceHalt mode) (false :: false :: false :: (leftColumns pairs.reverse ++ context)) resident) := by
  refine ⟨?_, return_chain mode context [] pairs resident, ?_, source_halt _ _ _⟩
  · simpa only [leftColumns, List.flatMap_nil, List.nil_append] using return_head mode context [] pairs resident
  · simpa only [List.append_nil] using return_last mode context [] pairs resident

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
