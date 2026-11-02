module

public import PaperProofs.Common.CompactPriceClaims

/-! Exact table-head/source-head identification. No machine cost is inferred. -/

@[expose] public section

namespace PaperProofs.Common.Native.CompactPrice.PSTRHeads

open PaperProofs.Common.SymbolicPrice PaperProofs.Structure PaperProofs.Structure.LaminarTree

/-- Finite scan of the original ordered compatibility sequence. -/
noncomputable def rankHeadIndices {Tool : Type*} [DecidableEq Tool] (full : List (Finset Tool))
    (remaining : Finset Tool) (target : ℕ∞) (offset : ℕ) : List ℕ :=
  ((List.finRange full.length).filter (fun stage =>
    decide (badChildRank (full.getD stage.val ∅) (full.drop (stage.val + 1)) remaining + 1 = target))).map
    (fun stage => offset + stage.val)

theorem heads_fst {Tool : Type*} [DecidableEq Tool]
    (stages : ExperimentSchedule Tool) (remaining : Finset Tool) (target : ℕ∞) (offset : ℕ) :
    (heads stages remaining target offset).map Prod.fst =
      rankHeadIndices (compatibility stages) remaining target offset := by
  induction stages generalizing offset with
  | nil => simp [heads, compatibility, rankHeadIndices]
  | cons stage later ih =>
    rcases stage with ⟨eligible, experiment⟩
    have hc : compatibility ((eligible, experiment) :: later) = eligible :: compatibility later := rfl
    rw [hc, rankHeadIndices]
    simp only [List.length_cons, List.finRange_succ, List.filter_cons, List.getD_cons_zero,
      Fin.val_zero, List.drop_succ_cons, List.drop_zero, List.filter_map, Function.comp_def,
      Fin.val_succ, List.getD_cons_succ, decide_eq_true_eq]
    rw [heads, executableBadRank_eq]
    split_ifs with h
    · simp only [List.map_cons, Fin.val_zero, Nat.add_zero, List.map_map,
        Function.comp_def, Fin.val_succ]
      congr 1
      simpa only [rankHeadIndices, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (offset + 1)
    · simp only [List.map_map, Function.comp_def, Fin.val_succ]
      simpa only [rankHeadIndices, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (offset + 1)

/-- Prefix-token serialization uses at most two data items per AST node. -/
theorem encodeExpr_length_le (expression : Expr) :
    (encodeExpr expression).length ≤ 2 * expression.nodes := by
  induction expression with
  | rational value => exact le_rfl
  | add left right ihl ihr | multiply left right ihl ihr | divide left right ihl ihr =>
    simp only [encodeExpr, List.length_cons, List.length_append, Expr.nodes]
    omega
  | log argument ih =>
    simp only [encodeExpr, List.length_cons, Expr.nodes]
    omega
end PaperProofs.Common.Native.CompactPrice.PSTRHeads



