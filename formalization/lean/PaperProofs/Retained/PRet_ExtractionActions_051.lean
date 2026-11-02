module

public import PaperProofs.Retained.PRet_FreshExtractionPolicy_047
public import PaperProofs.Retained.PRet_ActionOrigins_019

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetExtractionActions051

open Common Common.Native PRetInformationPackets006 PRetEntryReplay045
open PRetDelayedPolicy010 PRetActionOrigins019

variable {I : Instance}

theorem candidate_review (first : ℕ) (cached : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage)
    (h : PRetFreshExtractionPolicy047.candidate first cached sourceAction history = .review stage) :
    cached.halted = false ∧ sourceAction = .review (I.freshStageLift first stage) := by
  cases hhalt : cached.halted with
  | true =>
    simp only [PRetFreshExtractionPolicy047.candidate, hhalt, ↓reduceIte] at h
    split_ifs at h
    have hn := catchUp_review history _ _ stage h
    cases hn
  | false =>
    refine ⟨rfl, ?_⟩
    cases sourceAction with
    | review original =>
      by_cases hf : first ≤ original.val
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        have hn := catchUp_review history _ _ stage h
        cases hn
        rw [freshStageLift_suffixStageOf]
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        cases h
    | write original bit =>
      by_cases hf : first ≤ original.val
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        have hn := catchUp_review history _ _ stage h
        cases hn
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        cases h
    | allocate | execute | advance | stop | abandon =>
      simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte] at h
      cases h

theorem candidate_write (first : ℕ) (cached : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage) (bit : Bool)
    (h : PRetFreshExtractionPolicy047.candidate first cached sourceAction history = .write stage bit) :
    cached.halted = false ∧ sourceAction = .write (I.freshStageLift first stage) bit := by
  cases hhalt : cached.halted with
  | true =>
    simp only [PRetFreshExtractionPolicy047.candidate, hhalt, ↓reduceIte] at h
    split_ifs at h
    have hn := catchUp_write history _ _ stage bit h
    cases hn
  | false =>
    refine ⟨rfl, ?_⟩
    cases sourceAction with
    | review original =>
      by_cases hf : first ≤ original.val
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        have hn := catchUp_write history _ _ stage bit h
        cases hn
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        cases h
    | write original written =>
      by_cases hf : first ≤ original.val
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        have hn := catchUp_write history _ _ stage bit h
        cases hn
        rw [freshStageLift_suffixStageOf]
      · simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte, hf] at h
        cases h
    | allocate | execute | advance | stop | abandon =>
      simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte] at h
      cases h
theorem catchUp_no_correction {J : Instance} (history : List (VisibleEvent J)) (destination : ℕ)
    (next : Action J) (hnext : isCorrection next = false) :
    isCorrection (catchUp history destination next) = false := by
  cases hc : isCorrection (catchUp history destination next) with
  | false => rfl
  | true =>
    have hn := (catchUp_correction history destination next hc).2
    exact False.elim (Bool.false_ne_true (hnext.symm.trans hn))

theorem candidate_no_correction (first : ℕ) (cached : Startup I) (sourceAction : Action I)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    isCorrection (PRetFreshExtractionPolicy047.candidate first cached sourceAction history) = false := by
  cases hhalt : cached.halted with
  | true =>
    simp only [PRetFreshExtractionPolicy047.candidate, hhalt, ↓reduceIte]
    split_ifs
    · rfl
    · exact catchUp_no_correction history _ _ rfl
    · rfl
  | false =>
    cases sourceAction with
    | review original =>
      simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact catchUp_no_correction history _ _ rfl
      · rfl
    | write original bit =>
      simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte]
      split_ifs
      · exact catchUp_no_correction history _ _ rfl
      · rfl
    | allocate | execute | advance | stop | abandon =>
      simp only [PRetFreshExtractionPolicy047.candidate, hhalt, Bool.false_eq_true, ↓reduceIte]
      rfl
theorem rule_no_correction {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (startup : Startup I) (seed : Seed)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    isCorrection (PRetFreshExtractionPolicy047.rule first accounting source startup seed history) = false := by
  unfold PRetFreshExtractionPolicy047.rule PRetRetainedGuard007.guarded
  split_ifs
  · unfold PRetFreshExtractionPolicy047.raw
    cases hs : shadowFrom first accounting source startup seed history with
    | none => rfl
    | some cached => exact candidate_no_correction first cached _ history
  · rfl

theorem guarded_eq_raw {Seed : Type*} (first : ℕ) (accounting : NormalAccounting I)
    (source : PolicyRule I Seed) (startup : Startup I) (seed : Seed)
    (history : List (VisibleEvent (I.freshSuffix first))) (action : Action (I.freshSuffix first))
    (hne : action ≠ .abandon)
    (h : PRetFreshExtractionPolicy047.rule first accounting source startup seed history = action) :
    PRetFreshExtractionPolicy047.raw first accounting source startup seed history = action := by
  unfold PRetFreshExtractionPolicy047.rule PRetRetainedGuard007.guarded at h
  split_ifs at h
  · exact h
  · exact False.elim (hne h.symm)

end PaperProofs.Retained.PRetExtractionActions051


