module
public import Structure.RootB23_GenericRank_FiniteData_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option pp.explicit true
@[expose] public section
namespace RootB23.GenericRank

theorem drive_add {q : ℕ} (first later : ℕ) (state : State q) :
    drive (first+later) state=drive later (drive first state) := by
  induction first generalizing state with
  | zero => simp only [Nat.zero_add,drive]
  | succ first ih =>
    rw [Nat.add_right_comm]
    exact ih (tick state)

theorem drive_halted {q : ℕ} (count : ℕ) (state : State q) (halted : next state=none) :
    drive count state=state := by
  induction count with
  | zero => rfl
  | succ count ih => simpa only [drive,halted,Option.getD_none] using ih

theorem structuralFactor_mono {small large q : ℕ} (bound : small≤large) :
    structuralFactor small q≤structuralFactor large q := by
  have exponent:=Nat.pow_le_pow_right (show 0<q+2 by omega) (Nat.add_le_add_right bound 1)
  exact Nat.mul_le_mul (Nat.add_le_add_right bound 1) exponent

/-- Any suffix uses the SAME original F, including stage≥N and q=0.
No rank/answer/fuel oracle is an input. The canonical bound is calculated
only from the original incidence dimensions. The actual process halts
earlier, as witnessed by Run with next final=none. -/
theorem original_suffix_dfs (I : PaperProofs.Common.Instance) (stage : ℕ) (remaining : Finset I.Tool) :
    ∃ steps final,
      Run I.stageCount ⟨.call (I.compatibility.drop stage) remaining,[]⟩ final steps ∧
      steps≤3*PaperProofs.Common.Native.RationalControllerComputation.generalStructureFactor I ∧
      drive steps ⟨.call (I.compatibility.drop stage) remaining,[]⟩=final ∧
      drive (3*PaperProofs.Common.Native.RationalControllerComputation.generalStructureFactor I)
        ⟨.call (I.compatibility.drop stage) remaining,[]⟩=final ∧
      next final=none ∧
      final.control=.answer (PaperProofs.Structure.genericRank (I.compatibility.drop stage) remaining)
        (match I.compatibility.drop stage with
        | [] => none
        | eligible::later => PaperProofs.Structure.pickGenericMaxRankTool I.toolCount eligible later remaining) ∧
      (∀ clock, WellFormed I.stageCount (drive clock ⟨.call (I.compatibility.drop stage) remaining,[]⟩) ∧
        cells (drive clock ⟨.call (I.compatibility.drop stage) remaining,[]⟩)≤workspace I.stageCount I.toolCount) ∧
      (∀ clock rank, rank∈stateRanks (drive clock ⟨.call (I.compatibility.drop stage) remaining,[]⟩) →
        ∃ code : Fin (I.stageCount+2),decodeRank I.stageCount code.val=rank) := by
  obtain ⟨steps,final,run,actual,halted,correct,cost⟩:=
    dfs_actual I.toolCount (I.compatibility.drop stage) remaining
  have suffixBound : (I.compatibility.drop stage).length≤I.stageCount := by
    change (I.compatibility.drop stage).length≤I.compatibility.length
    rw [List.length_drop]
    exact Nat.sub_le _ _
  have factor:=Nat.mul_le_mul_left 3 (structuralFactor_mono (q := I.toolCount) suffixBound)
  have totalCost : steps≤3*PaperProofs.Common.Native.RationalControllerComputation.generalStructureFactor I :=
    cost.trans factor
  have initial : WellFormed I.stageCount
      (⟨.call (I.compatibility.drop stage) remaining,[]⟩ : State I.toolCount) := ⟨trivial,suffixBound⟩
  refine ⟨steps,final,run.weaken suffixBound,totalCost,actual,?_,halted,?_,?_,?_⟩
  · have fuel:=Nat.add_sub_of_le totalCost
    rw [←fuel,drive_add,actual]
    exact drive_halted _ final halted
  · cases equation : I.compatibility.drop stage with
    | nil => simpa only [equation] using correct
    | cons eligible later => simpa only [equation] using correct
  · intro clock
    have valid:=drive_wellFormed clock _ initial
    exact ⟨valid,wellFormed_cells _ valid⟩
  · intro clock rank member
    have valid:=drive_wellFormed clock _ initial
    exact rank_finite_representation I.stageCount rank (state_ranks_bound _ valid rank member)

end RootB23.GenericRank
