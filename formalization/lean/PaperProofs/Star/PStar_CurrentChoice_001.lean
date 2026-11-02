module

public import PaperProofs.Star.PStarLR_ToolChoice_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentChoice001

open Common Common.Native Parameters

/-- The ORIGINAL current Star selector always returns a compatible tool;
none remains a real unavailable-tool failure, not a fictitious repair. -/
theorem currentToolChoice_compatible (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (tool : Fin P.tools)
    (chosen : P.currentToolChoice order history stage = some tool) :
    tool ∈ (starInstance P.tools order).eligible stage := by
  classical
  change @Eq (Option (Fin P.tools)) (P.currentToolChoice order history stage) (some tool) at chosen
  rw [eligible_formula]
  cases label : stageLabel P.tools order stage with
  | none => exact Finset.mem_univ tool
  | some own =>
    unfold Parameters.currentToolChoice at chosen
    rw [label] at chosen
    dsimp only at chosen ⊢
    by_cases blocked : (historyCommitments history).any (fun pair => pair.2.val == own.val) = true
    · rw [ite_eq_left blocked] at chosen
      cases chosen
    · rw [ite_eq_right blocked] at chosen
      have heq := Option.some.inj chosen
      rw [heq]
      exact Finset.mem_singleton_self tool

/-- Selection checks the actual complete commitment log. The first
universal tool and every singleton tool keep the original Fin identities. -/
theorem currentToolChoice_commitment_any_false (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (tool : Fin P.tools)
    (chosen : P.currentToolChoice order history stage = some tool) :
    (historyCommitments history).any (fun pair => pair.2.val == tool.val) = false := by
  classical
  change @Eq (Option (Fin P.tools)) (P.currentToolChoice order history stage) (some tool) at chosen
  unfold Parameters.currentToolChoice at chosen
  cases label : stageLabel P.tools order stage with
  | some own =>
    rw [label] at chosen
    dsimp only at chosen ⊢
    by_cases blocked : (historyCommitments history).any (fun pair => pair.2.val == own.val) = true
    · rw [ite_eq_left blocked] at chosen
      cases chosen
    · rw [ite_eq_right blocked] at chosen
      have heq := Option.some.inj chosen
      rw [← heq]
      exact Bool.eq_false_iff.mpr blocked
  | none =>
    rw [label] at chosen
    cases order with
    | universalFirst =>
      dsimp only at chosen
      by_cases blocked : (historyCommitments history).any (fun pair => pair.2.val == 0) = true
      · rw [ite_eq_left blocked] at chosen
        cases chosen
      · rw [ite_eq_right blocked] at chosen
        have heq : P.firstTool = tool := Option.some.inj chosen
        rw [← heq]
        exact Bool.eq_false_iff.mpr blocked
    | singletonsFirst =>
      dsimp only at chosen
      have member := PStarLR.firstOfFinset_mem (Finset.univ.filter fun candidate : Fin P.tools =>
        !(historyCommitments history).any (fun pair => pair.2.val == candidate.val)) tool chosen
      have notUsed := (Finset.mem_filter.mp member).2
      cases hused : (historyCommitments history).any (fun pair => pair.2.val == tool.val) with
      | false => rfl
      | true => rw [hused] at notUsed; cases notUsed

/-- The concrete public selector never reuses an already committed tool,
including earlier current-window corrections on ultimately failing paths. -/
theorem currentToolChoice_unused (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (tool : Fin P.tools)
    (chosen : P.currentToolChoice order history stage = some tool) : tool ∉ historyUsed history := by
  have unused := currentToolChoice_commitment_any_false P order history stage tool chosen
  intro used
  obtain ⟨pair, member, equalTool⟩ := List.mem_map.mp (List.mem_toFinset.mp used)
  apply (List.any_eq_false.mp unused) pair member
  exact beq_iff_eq.mpr (congrArg Fin.val equalTool)

/-- The selected universal current tool in the original universal-first
script is literally Fin0, even if the contract permits deferred execution. -/
theorem currentToolChoice_universalFirst_identity (P : PaperProofs.Star.Parameters)
    (history : List (VisibleEvent (starInstance P.tools .universalFirst)))
    (stage : (starInstance P.tools .universalFirst).Stage) (tool : Fin P.tools)
    (universal : stageLabel P.tools .universalFirst stage = none)
    (chosen : P.currentToolChoice .universalFirst history stage = some tool) : tool.val = 0 := by
  change @Eq (Option (Fin P.tools)) (P.currentToolChoice .universalFirst history stage) (some tool) at chosen
  unfold Parameters.currentToolChoice at chosen
  rw [universal] at chosen
  dsimp only at chosen
  by_cases blocked : (historyCommitments history).any (fun pair => pair.2.val == 0) = true
  · rw [ite_eq_left blocked] at chosen
    cases chosen
  · rw [ite_eq_right blocked] at chosen
    have heq : P.firstTool = tool := Option.some.inj chosen
    rw [← heq]
    rfl

theorem currentToolChoice_singleton_identity (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (tool label : Fin P.tools)
    (singleton : stageLabel P.tools order stage = some label)
    (chosen : P.currentToolChoice order history stage = some tool) : tool.val = label.val := by
  have compatible := currentToolChoice_compatible P order history stage tool chosen
  rw [eligible_formula, singleton] at compatible
  exact congrArg Fin.val (Finset.mem_singleton.mp compatible)

end PaperProofs.Star.PStarCurrentChoice001
