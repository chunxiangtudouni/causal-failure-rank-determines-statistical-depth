module

public import Common.PSTR_TM_WordPriorFront_215
public import Common.PSTR_SYM_NaturalExportJoined_091

/-! The actual frozen215 run, not a caller-supplied prior archive, enters
a genuine reusable TM2 port. Its old HALT head push/gotoReturn is charged;
the original nonblank fee/right suffix remains part of the whole Tape. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicWordPriorStack

open Turing PaperProofs.Common.Native PaperProofs.Statistics PSTRWordVM PSTRTMWordPriorFront215

abbrev Store := VirtualBool.OldStore (states := 83)
abbrev State (C : Type*) := VirtualReturn.State C Store
abbrev Statement (C : Type*) := VirtualReturn.Statement C Store

def source : Unit → VirtualReturn.SmallStatement Store := VirtualBool.source priorMachine

def program {C : Type*} (caller : Statement C) : Fin 2 → Statement C := VirtualReturn.program source caller

theorem actual_original_prior_stack {C : Type*} (caller : Statement C) (context : C)
    (background : Fin 16 → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (path : List (State C)) (final : State C),
      path.head? = some (VirtualReturn.configuration context background
        (TM2.init (Γ := PSTRWordBool.PushPop.Alphabet) (Λ := Unit) (σ := Store) 0 (wordInput E target word))) ∧
      path.IsChain (fun before after => TM2.step (program caller) before = some after) ∧
      path.getLast? = some final ∧ final.l = some 1 ∧
      (VirtualBool.representedState final).Tape = Tape.mk₂
        (PA17TMRatArithmeticParse002.bothLeft
          (false :: PA17TMRatArithmeticParse002.sign E.priorOne :: priorBase E target word)
          (PA17TMRatArithmeticParse002.numeratorDigits E.priorOne)
          (PA17TMRatArithmeticParse002.denominatorDigits E.priorOne)) (afterPrior E target word) ∧
      path.length ≤ 33*((wordInput E target word).length+1)^2 ∧
      (∀ current ∈ path, current.var.1 = context ∧
        ∀ slot, slot ≠ 0 → slot ≠ 1 → current.stk slot = background slot) ∧
      ∀ current ∈ path, VirtualReturn.occupiedSlots current.stk ≤ VirtualReturn.outside background+
        128*((wordInput E target word).length+1)^2 := by
  have actual := prior_runs E target word
  obtain ⟨path,final,first,chain,last,returned,represented,_order,length,_context,frames,mass⟩ :=
    VirtualBool.same_old_run priorMachine caller context background (wordInput E target word)
      (priorTrace E target word) (priorFinal E target word)
      actual.1 actual.2.1 actual.2.2.1 actual.2.2.2.1
  have tape := congrArg TM0.Cfg.Tape represented
  rw [prior_final_tape] at tape
  have space := prior_prefix_space_le E target word (priorTrace E target word).length
  simp only [List.take_length] at space
  have time := prior_time_le E target word
  have positive : 1 ≤ ((wordInput E target word).length+1)^2 :=
    Nat.pow_le_pow_left (show 1 ≤ (wordInput E target word).length+1 by omega) 2
  refine ⟨path,final,first,chain,last,returned,tape,?_,frames,?_⟩
  · rw [length]
    omega
  · intro current present
    exact (mass current present).trans (Nat.add_le_add_left space _)

theorem body_at_entry {C : Type*} (caller : Statement C) :
    program caller 0 = VirtualReturn.statement (source ()) := rfl

theorem source_actions {C : Type*} : PSTRWordBool.ScannerClock.actions
    (VirtualReturn.statement (C := C) (source ())) = 4 := VirtualBool.actions priorMachine

theorem source_pushes {C : Type*} : PSTRWordBool.AuxWorkspace.pushes
    (VirtualReturn.statement (C := C) (source ())) = 2 := VirtualBool.pushes priorMachine

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicWordPriorStack
