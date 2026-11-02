module

public import Structure.PA17_TM_Division_Loop_002d

/-! Fixed commit control and transport of the already verified return path.
The two actual machines are commitMachine false and commitMachine true;
emit is a finite code choice, never an input tape answer or numeric parameter. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
open PSTRTMCompareCode054 PSTRTMBinaryAdd024

def commitLabel (q : Fin 28) : Fin 34 := ⟨q.val, by omega⟩
def commitCfg (state : MachineState 27) : MachineState 33 := ⟨commitLabel state.q, state.Tape⟩
def commitState (label : Fin 34) (left right : List Bool) : MachineState 33 :=
  ⟨label, Turing.Tape.mk₂ left right⟩

def commitMachine (emit : Bool) : Machine 33 := fun q symbol =>
  if hold : q.val < 28 then
    if q.val = 9 then some (28, .write emit)
    else (sourceMachine ⟨q.val, hold⟩ symbol).map (fun (next, command) => (commitLabel next, command))
  else match q.val with
    | 28 => some (29, .move .right)
    | 29 => some (30, .move .right)
    | 30 => some (31, .write false)
    | 31 => some (32, .move .left)
    | 32 => some (33, .move .left)
    | 33 => some (commitLabel (returnSource 1), .write symbol)
    | _ => none

theorem commit_step_lift (emit : Bool) (state : MachineState 27) (hnine : state.q.val ≠ 9) :
    Turing.TM0.step (commitMachine emit) (commitCfg state) =
      (Turing.TM0.step sourceMachine state).map commitCfg := by
  rcases state with ⟨q,tape⟩
  unfold Turing.TM0.step commitMachine commitCfg commitLabel
  simp only [q.isLt, ↓reduceDIte, hnine, ↓reduceIte, Fin.eta]
  cases hs : sourceMachine q tape.head with
  | none => simp
  | some pair =>
    rcases pair with ⟨next,command⟩
    cases command <;> simp

theorem return_labels (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool))
    (resident : List Bool) (state : MachineState 27) (hstate : state ∈ returnTrace mode context previous pairs resident) :
    10 ≤ state.q.val := by
  induction pairs generalizing previous with
  | nil =>
    simp only [returnTrace, returnEndTrace, List.mem_cons, List.not_mem_nil, or_false] at hstate
    rcases hstate with rfl | rfl | rfl | rfl <;>
      simp [sourceState, returnSource, returnFlagA, returnLabel, returnHop, sourceHalt] <;> omega
  | cons pair later ih =>
    rcases pair with ⟨a,b⟩
    simp only [returnTrace, List.mem_append] at hstate
    rcases hstate with hstate | hstate
    · simp only [returnUnitTrace, List.mem_cons, List.not_mem_nil, or_false] at hstate
      rcases hstate with rfl | rfl | rfl | rfl <;>
        simp [sourceState, returnSource, returnFlagA, returnPending, returnFlagB, returnLabel] <;> omega
    · exact ih ((a,b) :: previous) hstate

def commitReturnTrace (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool))
    (resident : List Bool) : List (MachineState 33) :=
  (returnTrace mode context previous pairs resident).map commitCfg

theorem commit_return_head (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (commitReturnTrace mode context previous pairs resident).head? = some
      (commitState (commitLabel (returnSource mode)) (leftColumns previous ++ context)
        (operandColumns pairs ++ false :: false :: false :: resident)) := by
  simp only [commitReturnTrace, List.head?_map, return_head, Option.map_some]
  rfl

theorem commit_return_last (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (commitReturnTrace mode context previous pairs resident).getLast? = some
      (commitState (commitLabel (sourceHalt mode))
        (false :: false :: false :: (leftColumns (pairs.reverse ++ previous) ++ context)) resident) := by
  simp only [commitReturnTrace, List.getLast?_map, return_last, Option.map_some]
  rfl

theorem commit_return_length (mode : Fin 3) (context : List Bool) (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (commitReturnTrace mode context previous pairs resident).length = 4 * pairs.length + 4 := by
  simp only [commitReturnTrace, List.length_map, return_length]

theorem commit_return_chain (emit : Bool) (mode : Fin 3) (context : List Bool)
    (previous pairs : List (Bool × Bool)) (resident : List Bool) :
    (commitReturnTrace mode context previous pairs resident).IsChain
      (fun before after => Turing.TM0.step (commitMachine emit) before = some after) := by
  apply (List.isChain_map _).mpr
  apply (return_chain mode context previous pairs resident).imp_of_mem_imp
  intro before after hb _ hs
  have hq := return_labels mode context previous pairs resident before hb
  rw [commit_step_lift emit before (by omega), hs]
  rfl

theorem commit_halt (emit : Bool) (mode : Fin 3) (left right : List Bool) :
    Turing.TM0.step (commitMachine emit) (commitState (commitLabel (sourceHalt mode)) left right) = none := by
  change Turing.TM0.step (commitMachine emit) (commitCfg (sourceState (sourceHalt mode) left right)) = none
  rw [commit_step_lift emit _ (by simp [sourceState, sourceHalt]; omega), source_halt]
  rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
