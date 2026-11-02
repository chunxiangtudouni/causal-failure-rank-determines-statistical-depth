module

public import PaperProofs.Paid.PDLower_Allowance_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u}


theorem paidRunPosteriorError_range (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (sample : Seed × (P.input fee hf).World)
    (stage : P.sharedInstance.Stage) :
    0 ≤ P.paidRunPosteriorError fee hf C mode accounting rule sample stage ∧
      P.paidRunPosteriorError fee hf C mode accounting rule sample stage ≤ 1 / 2 := by
  unfold Parameters.paidRunPosteriorError
  dsimp only
  split_ifs
  · constructor <;> norm_num
  · constructor <;> norm_num
  · exact ⟨(P.binarySymmetric.wordPosteriorError_pos _).le, P.binarySymmetric.wordPosteriorError_le_half _⟩

variable [MeasurableSpace Seed]

theorem measurable_paidRunPosteriorError (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee)
    (C : P.PaymentContract) (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance)
    (rule : PolicyRule P.sharedInstance Seed) (hm : MeasurableRule rule) (stage : P.sharedInstance.Stage) :
    Measurable (fun sample => ENNReal.ofReal (P.paidRunPosteriorError fee hf C mode accounting rule sample stage)) := by
  classical
  have hword : Measurable (fun pair : ℕ∞ × P.experiment.Tape =>
      (⟨pair.1.toNat, fun k => pair.2 k.val⟩ : P.experiment.StoppedWord)) := by
    apply measurable_from_prod_countable_right
    intro count
    have hv : Measurable (fun tape : P.experiment.Tape => fun k : Fin count.toNat => tape k.val) :=
      measurable_pi_iff.mpr (fun k => measurable_pi_apply k.val)
    exact (measurable_of_countable (fun word : Fin count.toNat → Fin P.experiment.alphabetSize =>
      (⟨count.toNat, word⟩ : P.experiment.StoppedWord))).comp hv
  have hmap : Measurable (fun sample : Seed × (P.input fee hf).World =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorError
        (⟨(P.paidRunReviewCount fee hf C mode accounting rule sample stage).toNat,
          fun k => (sample.2 stage).2 k.val⟩ : P.experiment.StoppedWord))) :=
    (measurable_of_countable (fun word : P.experiment.StoppedWord =>
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorError word))).comp
      (hword.comp ((measurable_paidRunReviewCount P fee hf C mode accounting rule hm stage).prodMk
        ((measurable_pi_apply stage).comp measurable_snd).snd))
  have hcount := measurable_paidRunReviewCount P fee hf C mode accounting rule hm stage
  have hzero : MeasurableSet {sample | P.paidRunReviewCount fee hf C mode accounting rule sample stage = 0} :=
    (measurableSet_singleton (0 : ℕ∞)).preimage hcount
  have htop : MeasurableSet {sample | P.paidRunReviewCount fee hf C mode accounting rule sample stage = ⊤} :=
    (measurableSet_singleton (⊤ : ℕ∞)).preimage hcount
  have hfinal : Measurable (fun sample : Seed × (P.input fee hf).World =>
      if P.paidRunReviewCount fee hf C mode accounting rule sample stage = 0 then ENNReal.ofReal (1 / 2 : ℝ)
      else if P.paidRunReviewCount fee hf C mode accounting rule sample stage = ⊤ then (0 : ℝ≥0∞)
      else ENNReal.ofReal (P.binarySymmetric.wordPosteriorError
        (⟨(P.paidRunReviewCount fee hf C mode accounting rule sample stage).toNat,
          fun k => (sample.2 stage).2 k.val⟩ : P.experiment.StoppedWord))) :=
    measurable_const.ite hzero (measurable_const.ite htop hmap)
  convert hfinal using 1
  funext sample
  unfold Parameters.paidRunPosteriorError
  dsimp only
  split_ifs
  · rfl
  · exact ENNReal.ofReal_zero
  · rfl

end PDLower