module

public import PaperProofs.Paid.PDLower_BlindRetarget_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native

namespace PDLower

variable {I : Instance}

def AllWrittenWrong (ledger : Ledger I) : Prop :=
  ∀ stage bit, ledger.written stage = some bit → bit ≠ ledger.truth stage

theorem allWrittenWrong_not_success (C : Contract I) (ledger : Ledger I)
    (hshort : I.toolCount < I.stageCount) (wellFormed : LedgerWellFormed ledger)
    (wrong : AllWrittenWrong ledger) : ¬ ledger.success C := by
  intro success
  have cover : (Finset.univ : Finset I.Stage) ⊆
      (ledger.executions.map (fun execution => execution.handle.stage)).toFinset := by
    intro stage _hstage
    rcases success.2.2.2 stage with correct | corrected
    · exact ((wrong stage (ledger.truth stage) correct) rfl).elim
    · obtain ⟨execution, hmem, hstage⟩ := corrected
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨execution, hmem, hstage⟩)
  have hcount : I.stageCount ≤ ledger.executions.length := by
    calc
      I.stageCount = (Finset.univ : Finset I.Stage).card := by
        simp only [Finset.card_univ, Instance.Stage, Fintype.card_fin, Instance.stageCount]
      _ ≤ (ledger.executions.map (fun execution => execution.handle.stage)).toFinset.card :=
        Finset.card_le_card cover
      _ ≤ (ledger.executions.map (fun execution => execution.handle.stage)).length := List.toFinset_card_le _
      _ = ledger.executions.length := by simp only [List.length_map]
  have htools : ledger.executions.length ≤ I.toolCount :=
    (Ledger.execution_count_le wellFormed).trans (min_le_right _ _)
  omega

theorem runSuccess_iff_success_of_halted (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (sample : Seed × input.World) (clock : ℕ)
    (halted : (run input C mode accounting rule sample clock).halted = true) :
    runSuccess input C mode accounting rule sample ↔
      (run input C mode accounting rule sample clock).ledger.success C := by
  constructor
  · rintro ⟨otherClock, otherHalted, otherSuccess⟩
    rcases le_total otherClock clock with hle | hle
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [run_after_halt input C mode accounting rule sample otherClock otherHalted extra]
      exact otherSuccess
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le hle
      rw [run_after_halt input C mode accounting rule sample clock halted extra] at otherSuccess
      exact otherSuccess
  · exact fun success => ⟨clock, halted, success⟩

end PDLower
