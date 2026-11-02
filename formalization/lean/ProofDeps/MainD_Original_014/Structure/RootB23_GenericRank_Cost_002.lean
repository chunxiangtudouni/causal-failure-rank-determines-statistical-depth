module
public import Structure.RootB23_GenericRank_Recurrence_001
public import PaperProofs.Common.RationalControllerComputation

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
@[expose] public section
namespace RootB23.GenericRank
open PaperProofs.Structure

theorem sum_children_le {q : ℕ} (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (tools : List (Fin q)) (limit : ℕ)
    (bound : ∀ available, (evaluate q stages available).nodes≤limit) :
    (tools.map (fun tool => (evaluate q stages (remaining.erase tool)).nodes)).sum≤tools.length*limit := by
  induction tools with
  | nil => simp only [List.map_nil,List.sum_nil,List.length_nil,Nat.zero_mul,le_refl]
  | cons tool later ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    have child:=bound (remaining.erase tool)
    omega

/-- Counts all recursive calls, including terminal and good-child calls.
This is a semantic counter, not a stack holding the execution history. -/
theorem evaluate_nodes_bound (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    (evaluate q stages remaining).nodes≤(q+2)^(stages.length+1) := by
  induction stages generalizing remaining with
  | nil => simp only [evaluate,List.length_nil,Nat.zero_add,pow_one];omega
  | cons eligible later ih =>
    rw [evaluate_nodes_cons]
    have children:=sum_children_le later remaining (genericRankCandidates q eligible remaining)
      ((q+2)^(later.length+1)) ih
    have length:=Nat.mul_le_mul_right ((q+2)^(later.length+1)) (candidates_length q eligible remaining)
    have good:=ih remaining
    have positive : 1≤(q+2)^(later.length+1) := Nat.one_le_pow _ _ (by omega)
    calc
      1+(evaluate q later remaining).nodes+
          ((genericRankCandidates q eligible remaining).map
            (fun tool => (evaluate q later (remaining.erase tool)).nodes)).sum
          ≤1+(q+2)^(later.length+1)+q*((q+2)^(later.length+1)) := by omega
      _≤(q+2)^(later.length+1)+(q+2)^(later.length+1)+q*((q+2)^(later.length+1)) := by omega
      _=(q+2)^(later.length+1)*(q+2) := by
        rw [Nat.mul_add,Nat.mul_comm ((q+2)^(later.length+1)) q]
        omega
      _=(q+2)^((eligible::later).length+1) := by
        simpa only [List.length_cons] using (pow_succ (q+2) (later.length+1)).symm

def structuralFactor (N q : ℕ) : ℕ := (N+1)*(q+2)^(N+1)

theorem evaluate_nodes_one_factor (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    (evaluate q stages remaining).nodes≤structuralFactor stages.length q := by
  apply (evaluate_nodes_bound q stages remaining).trans
  have factor:=Nat.mul_le_mul_right ((q+2)^(stages.length+1)) (show 1≤stages.length+1 by omega)
  simpa only [structuralFactor,Nat.one_mul] using factor

theorem original_factor (I : PaperProofs.Common.Instance) :
    structuralFactor I.compatibility.length I.toolCount=
      PaperProofs.Common.Native.RationalControllerComputation.generalStructureFactor I := rfl

theorem original_instance_nodes (I : PaperProofs.Common.Instance) (remaining : Finset I.Tool) :
    (evaluate I.toolCount I.compatibility remaining).nodes≤
      PaperProofs.Common.Native.RationalControllerComputation.generalStructureFactor I :=
  evaluate_nodes_one_factor I.toolCount I.compatibility remaining

/-- Every completed value belongs to a finite carrier with one top code
and finite values at most q+1; there is no unbounded rank answer oracle. -/
theorem evaluate_rank_finite_carrier (q : ℕ) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    (evaluate q stages remaining).rank=⊤ ∨ (evaluate q stages remaining).rank≤((q+1 : ℕ) : ℕ∞) := by
  rw [(evaluate_exact q stages remaining).1,genericRank_eq_errorRank]
  by_cases infinite : errorRank stages remaining=⊤
  · exact Or.inl infinite
  · apply Or.inr
    have bound:=errorRank_finite_le_card_add_one stages remaining infinite
    have card : remaining.card≤q := by simpa using Finset.card_le_univ remaining
    exact bound.trans (by exact_mod_cast Nat.add_le_add_right card 1)

end RootB23.GenericRank
