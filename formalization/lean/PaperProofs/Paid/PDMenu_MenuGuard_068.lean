module

public import PaperProofs.Paid.PDMenu_MenuRepairPermissions_067
public import PaperProofs.Common.NativeHorizon

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The literal compiler candidate passes the fixed visible guard on every
real prefix, even for an arbitrary numerical table. -/
theorem menuCandidateAction_allowed (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting (freshInstance N K))
    {Seed : Type*} (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C mode accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) :
    historyAllowsAction state.history (P.menuCandidateAction N K table menuSeed state.history) := by
  classical
  by_cases hh : historyHalted state.history = true
  · simp only [Parameters.menuCandidateAction, hh, ite_true, historyAllowsAction]
  · rw [Parameters.menuCandidateAction, ite_eq_right hh]
    by_cases hc : historyCursor state.history < N
    · rw [dite_eq_left hc]
      dsimp only
      let stage : (freshInstance N K).Stage := ⟨historyCursor state.history, by simpa [freshInstance] using hc⟩
      cases hw : historyWrite state.history stage with
      | none =>
        dsimp only
        have hopen : historyWritten state.history stage = none := by
          simp only [historyWritten, hw, Option.map_none]
        cases ha : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K state.history stage)).action with
        | finish => trivial
        | abandon => trivial
        | test level bad =>
          dsimp only
          dsimp only [Parameters.endpointTestingAction]
          split_ifs <;> first | exact ⟨rfl, hopen⟩ | trivial
      | some pair =>
        obtain ⟨bit, serial⟩ := pair
        dsimp only
        have hwritten : historyWritten state.history stage ≠ none := by
          simp only [historyWritten, hw, Option.map_some, ne_eq, reduceCtorEq, not_false_eq_true]
        cases hr : historyReport state.history stage with
        | none => trivial
        | some packet =>
          obtain ⟨observedTruth, reportedSerial⟩ := packet
          dsimp only
          split_ifs with hserial hbit
          · trivial
          · exact ⟨rfl, hwritten⟩
          · have hs : serial = reportedSerial := by simpa only [bne_iff_ne, not_not] using hserial
            have hb : bit ≠ observedTruth := by simpa only [beq_iff_eq] using hbit
            cases ha : (Parameters.menuEntryAt table (N - stage.val) (P.menuEntryTools N K state.history stage)).action with
            | finish => trivial
            | abandon => trivial
            | test level bad =>
              cases bad with
              | abandon => trivial
              | repair =>
                exact menuRepairAction_allowed P N K fee hfee C hearly mode accounting rule seed truth tapes hp stage
                  rfl hwritten (fun handle hv => menuVisibleHandle_valid state.history stage bit observedTruth
                    serial reportedSerial hw hr hs hb handle hv)
    · rw [dite_eq_right hc]
      split_ifs <;> trivial

theorem compiledMenuRule_eq_candidate_on_prefix (P : Parameters) (N K : ℕ) (table : MenuTable)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : Contract (freshInstance N K)) (hearly : C.reporting = .early)
    (accounting : NormalAccounting (freshInstance N K))
    {Seed : Type*} (rule : PolicyRule (freshInstance N K) Seed) (seed : Seed)
    (truth : (freshInstance N K).Stage → Bool) (tapes : ReviewTapes (P.freshInput N K fee hfee))
    {clock : ℕ} {state : State (freshInstance N K)}
    (hp : Prefix (P.freshInput N K fee hfee) C .uncapped accounting rule seed truth tapes clock state)
    (menuSeed : MenuSeed N K) :
    P.compiledMenuRule N K table menuSeed state.history = P.menuCandidateAction N K table menuSeed state.history := by
  exact ite_eq_left (menuCandidateAction_allowed P N K table fee hfee C hearly .uncapped accounting
    rule seed truth tapes hp menuSeed)

/-- Complete original D18 guard-nonbinding field, proved from genuine native
prefixes of the selected compiled script, with no performance premises. -/
theorem menuCompilerGuardNonbinding (P : Parameters) : P.MenuCompilerGuardNonbinding := by
  intro fee penalty hfee _ _ N K C hC accounting sample clock
  dsimp only
  intro hactive
  let table := P.solveMenuTable fee penalty K N
  let rule := P.compiledMenuRule N K table
  have hp := run_prefix_of_active (P.freshInput N K fee hfee) C .uncapped accounting rule
    (P.compiledMenuRule_uncapped_legal N K table fee hfee C hC.1.1 accounting) sample clock hactive
  exact compiledMenuRule_eq_candidate_on_prefix P N K table fee hfee C hC.1.1 accounting rule sample.1
    ((P.freshInput N K fee hfee).truthAt sample.2) (worldTapes (P.freshInput N K fee hfee) sample.2) hp sample.1

end PDMenu
