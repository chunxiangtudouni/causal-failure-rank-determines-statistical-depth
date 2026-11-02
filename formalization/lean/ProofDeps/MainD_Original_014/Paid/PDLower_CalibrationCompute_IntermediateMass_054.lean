module

public import Paid.PDLower_CalibrationCompute_IntermediateDen_053

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDLower.CalibrationCompute

def rowSuffixCommands (P : Parameters) (level : ℕ) (previous : Array ℚ) (cursor : ℕ) :
    List (WalkCell level × ℚ) :=
  ((List.finRange (2*level+1)).drop cursor).flatMap (fun state =>
    (List.finRange 2).map (fun letter =>
      (walkMove level state letter,previous.getD state.val 0*P.experiment.channel true letter)))

theorem rowCommands_split (P : Parameters) (level : ℕ) (previous : Array ℚ) (cursor : ℕ) :
    PDROC.endpointWalkCommands P level true previous=
      rowPrefixCommands P level previous cursor++rowSuffixCommands P level previous cursor := by
  unfold PDROC.endpointWalkCommands rowPrefixCommands rowSuffixCommands
  rw [←List.flatMap_append,List.take_append_drop]

theorem walkCommand_nonneg (P : Parameters) (level clock : ℕ) (states : List (WalkCell level))
    (command : WalkCell level × ℚ)
    (member : command ∈ states.flatMap (fun state => (List.finRange 2).map (fun letter =>
      (walkMove level state letter,(P.walkRow level true clock).getD state.val 0*P.experiment.channel true letter)))) :
    0≤command.2 := by
  obtain ⟨state,_stateMember,letterMember⟩ := List.mem_flatMap.mp member
  obtain ⟨letter,_letterMember,equation⟩ := List.mem_map.mp letterMember
  subst command
  exact mul_nonneg (PDROC.endpointWalkDistribution_nonneg P level true clock state)
    (P.experiment.channel_pos true letter).le

theorem scatter_getD_mono {width : ℕ} (commands : List (Fin width × ℚ)) (initial : Array ℚ)
    (size : initial.size=width) (masses : ∀ command∈commands,0≤command.2) (query : ℕ) :
    initial.getD query 0≤(PDROC.endpointArrayScatter commands initial).getD query 0 := by
  induction commands generalizing initial with
  | nil => exact le_rfl
  | cons command rest ih =>
    have inside : command.1.val < initial.size := by rw [size]; exact command.1.isLt
    have amount : 0≤(if command.1.val=query then command.2 else 0) := by
      split_ifs
      · exact masses command (by simp)
      · exact le_rfl
    have one : initial.getD query 0≤(PDROC.endpointArrayBump initial command.1.val command.2).getD query 0 := by
      rw [PDROC.endpointArrayBump_getD initial command.1.val query command.2 inside]
      exact le_add_of_nonneg_right amount
    have following := ih (PDROC.endpointArrayBump initial command.1.val command.2)
      (by simpa only [PDROC.endpointArrayBump_size] using size)
      (fun entry member => masses entry (by simp only [List.mem_cons]; exact Or.inr member))
    exact one.trans following

theorem zeroRow_getD (width query : ℕ) : (Array.replicate width (0 : ℚ)).getD query 0=0 := by
  by_cases inside : query<width <;>
    simp [Array.getD_eq_getD_getElem?,inside]

/-- Every actual state-prefix accumulator lies between zero and the
complete next-row mass. This is independent of how many source cells
have already been visited. -/
theorem rowScatterPrefix_bounds (P : Parameters) (level clock cursor : ℕ) (query : WalkCell level) :
    0≤(rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0 ∧
      (rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0≤1 := by
  let previous := P.walkRow level true clock
  let partialRow := rowScatterPrefix P level previous cursor
  have first := scatter_getD_mono (rowPrefixCommands P level previous cursor) (Array.replicate (2*level+1) 0)
    (Array.size_replicate ..) (fun command member => walkCommand_nonneg P level clock _ command member) query.val
  have nonnegative : 0≤partialRow.getD query.val 0 := by
    simpa only [zeroRow_getD,partialRow,rowScatterPrefix] using first
  have following := scatter_getD_mono (rowSuffixCommands P level previous cursor) partialRow
    (rowScatterPrefix_size ..) (fun command member => walkCommand_nonneg P level clock _ command member) query.val
  have complete : PDROC.endpointArrayScatter (rowSuffixCommands P level previous cursor) partialRow=
      P.walkUpdate level true previous := by
    rw [PDROC.walkUpdate_eq_endpointScatter,rowCommands_split P level previous cursor]
    simp only [partialRow,rowScatterPrefix,PDROC.endpointArrayScatter,List.foldl_append]
  rw [complete] at following
  have point := Finset.single_le_sum
    (f:=fun state : WalkCell level => P.walkDistribution level true (clock+1) state)
    (fun state _ => PDROC.endpointWalkDistribution_nonneg P level true (clock+1) state)
    (Finset.mem_univ query)
  rw [PDROC.endpointWalkDistribution_sum] at point
  have upper : (P.walkUpdate level true previous).getD query.val 0≤1 := by
    simpa only [walkDistribution,walkRow,previous] using point
  exact ⟨nonnegative,following.trans upper⟩

theorem rowScatterPrefix_numAbs_le_den (P : Parameters) (level clock cursor : ℕ) (query : WalkCell level) :
    ((rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0).num.natAbs≤
      ((rowScatterPrefix P level (P.walkRow level true clock) cursor).getD query.val 0).den := by
  have bounded := rowScatterPrefix_bounds P level clock cursor query
  exact PDROC.DataBits.ratNumAbs_le_den _ bounded.1 bounded.2

end PDLower.CalibrationCompute
