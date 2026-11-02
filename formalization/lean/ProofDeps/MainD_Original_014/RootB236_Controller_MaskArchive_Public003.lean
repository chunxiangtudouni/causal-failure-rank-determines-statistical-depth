module
public import RootB236_Controller_MaskArchive_Run002

/-! Two physical reverse-backup calls around a destructive mask consumer.
This leaf preserves the current parent mask; it does not decode original
input or implement a DFS frame stack. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB236.Controller.MaskArchive.Public
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM
variable {C : Type*}

def archiveRoles : Stack ≃ Stack := (Equiv.swap 0 4).trans ((Equiv.swap 2 8).trans (Equiv.swap 3 12))
def restoreRoles : Stack ≃ Stack := (Equiv.swap 0 8).trans ((Equiv.swap 2 4).trans (Equiv.swap 3 12))

def archive4To8 (caller : Statement C) : Label → Statement C := program archiveRoles caller
def restore8To4 (caller : Statement C) : Label → Statement C := program restoreRoles caller

def physicalBank (source destination : Stack) (background : Stack → List Bool)
    (input backup scratch : List Bool) : Stack → List Bool :=
  fun slot => if slot=source then input else if slot=destination then backup else if slot=12 then scratch else background slot
def physicalState (source destination : Stack) (background : Stack → List Bool) (point : Label)
    (memory : Store C) (input backup scratch : List Bool) : State C :=
  ⟨some point,memory,physicalBank source destination background input backup scratch⟩

theorem archive_state (background : Stack → List Bool) (point : Label) (memory : Store C)
    (input backup scratch : List Bool) : state archiveRoles background point memory input backup scratch=
      physicalState 4 8 background point memory input backup scratch := rfl
theorem restore_state (background : Stack → List Bool) (point : Label) (memory : Store C)
    (input backup scratch : List Bool) : state restoreRoles background point memory input backup scratch=
      physicalState 8 4 background point memory input backup scratch := rfl

theorem archive_frame (slot : Stack) : ¬Work archiveRoles slot ↔ slot≠4 ∧ slot≠8 ∧ slot≠12 := by
  change ¬(slot=4 ∨ slot=8 ∨ slot=12) ↔ _
  simp only [not_or]
theorem restore_frame (slot : Stack) : ¬Work restoreRoles slot ↔ slot≠8 ∧ slot≠4 ∧ slot≠12 := by
  change ¬(slot=8 ∨ slot=4 ∨ slot=12) ↔ _
  simp only [not_or]

/-- Arbitrary actual old target and scratch contents are preserved as
tails. The direction is reverse-prepend, not ordinary same-order COPY. -/
theorem archive4To8_general (caller : Statement C) (background : Stack → List Bool)
    (memory : Store C) (bits backup scratch : List Bool) :
    ∃ run,Facts archiveRoles caller background memory bits backup scratch run := actual _ _ _ _ _ _ _
theorem restore8To4_general (caller : Statement C) (background : Stack → List Bool)
    (memory : Store C) (bits backup scratch : List Bool) :
    ∃ run,Facts restoreRoles caller background memory bits backup scratch run := actual _ _ _ _ _ _ _

theorem archive4To8_actual (caller : Statement C) (background : Stack → List Bool)
    (memory : Store C) (remainingMask : List Bool) :
    ∃ run,Facts archiveRoles caller background memory remainingMask [] [] run ∧
      run.head?=some (physicalState 4 8 background .boot memory remainingMask [] []) ∧
      run.getLast?=some (physicalState 4 8 background .done (memory.1,true,true)
        remainingMask remainingMask.reverse []) := by
  obtain ⟨run,facts⟩:=archive4To8_general caller background memory remainingMask [] []
  refine ⟨run,facts,?_,?_⟩
  · simpa only [archive_state] using facts.first
  · simpa only [archive_state,List.append_nil] using facts.last

/-- The program really scans reverse-mask8 and copies its reverse into
empty4. reverse_reverse is used only to identify the proved output. -/
theorem restore8To4_actual (caller : Statement C) (background : Stack → List Bool)
    (memory : Store C) (remainingMask : List Bool) :
    ∃ run,Facts restoreRoles caller background memory remainingMask.reverse [] [] run ∧
      run.head?=some (physicalState 8 4 background .boot memory remainingMask.reverse [] []) ∧
      run.getLast?=some (physicalState 8 4 background .done (memory.1,true,true)
        remainingMask.reverse remainingMask []) := by
  obtain ⟨run,facts⟩:=restore8To4_general caller background memory remainingMask.reverse [] []
  refine ⟨run,facts,?_,?_⟩
  · simpa only [restore_state] using facts.first
  · simpa only [restore_state,List.append_nil,List.reverse_reverse] using facts.last

theorem archive4To8_supports (caller : Statement C) : TM2.Supports (archive4To8 caller) support := supports _ _
theorem restore8To4_supports (caller : Statement C) : TM2.Supports (restore8To4 caller) support := supports _ _
theorem archive4To8_done (caller : Statement C) : archive4To8 caller .done=caller := rfl
theorem restore8To4_done (caller : Statement C) : restore8To4 caller .done=caller := rfl

private theorem identity_statement (body : Statement C) : StackIso.statement (Equiv.refl Stack) body=body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => simp only [StackIso.statement,Equiv.refl_apply,ih]
  | branch _ _ _ yes no => simp only [StackIso.statement,yes,no]
  | goto _ | halt => rfl
private theorem identity_configuration (current : State C) : StackIso.configuration (Equiv.refl Stack) current=current := by
  cases current;rfl

/-- A literal combined code may replace done by a caller. No proper
boundary executes it; only already executed callee statements are charged. -/
theorem caller_chain {roles : Stack ≃ Stack} {caller : Statement C} {background : Stack → List Bool}
    {memory : Store C} {input backup scratch : List Bool} {run : List (State C)}
    (facts : Facts roles caller background memory input backup scratch run)
    (code : Label → Statement C) (same : ∀ point,point≠.done→code point=program roles caller point) :
    run.IsChain (fun a b => TM2.step code a=some b) := by
  have mapped:=StackIso.chain_configuration_on (Equiv.refl Stack) (program roles caller) code run facts.chain
    (by
      intro current member point selected
      rw [identity_statement]
      apply same point
      intro equal
      subst point
      exact (facts.proper current member).1 selected)
  rw [List.map_id'' identity_configuration run] at mapped
  exact mapped

def terminal (roles : Stack ≃ Stack) (background : Stack → List Bool) (memory : Store C)
    (input backup scratch : List Bool) : State C := ⟨none,(memory.1,true,true),bank roles background input (input.reverse++backup) scratch⟩
theorem return_halts (roles : Stack ≃ Stack) (background : Stack → List Bool) (memory : Store C)
    (input backup scratch : List Bool) :
    TM2.step (program roles .halt) (state roles background .done (memory.1,true,true) input (input.reverse++backup) scratch)=
      some (terminal roles background memory input backup scratch) := rfl
theorem terminal_halt (roles : Stack ≃ Stack) (background : Stack → List Bool) (memory : Store C)
    (input backup scratch : List Bool) : TM2.step (program roles .halt) (terminal roles background memory input backup scratch)=none := rfl

/-- Source/support are fixed before all physical input, frame and memory.
This is a reusable current-mask leaf, not an original-input DFS theorem. -/
theorem fixed_source (C : Type*) (roles : Stack ≃ Stack) :
    ∃ source : Label → Statement C,source .done=.halt ∧ TM2.Supports source support ∧
      ∀ background memory input backup scratch,
      ∃ run,Facts roles (.halt : Statement C) background memory input backup scratch run ∧
        run.IsChain (fun a b => TM2.step source a=some b) := by
  refine ⟨program roles .halt,rfl,supports _ _,?_⟩
  intro background memory input backup scratch
  obtain ⟨run,facts⟩:=actual roles .halt background memory input backup scratch
  exact ⟨run,facts,facts.chain⟩

end RootB236.Controller.MaskArchive.Public
