module

public import PaperProofs.Structure.LaminarRankExtraction
public import PaperProofs.Structure.Rank
public import Mathlib.Data.List.MinMax
public import Init.Data.List.FinRange

/-!
Executable maximum-rank tool extraction from the same stored full-input table.
The finite candidate list is filtered from Fin q; Mathlib's argmax compares
computed ranks. The specification uses the independent causal-play rank.
This is a semantic strategy step, with no O(t) tree-descent cost claim.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

def availableToolList (q : Nat) (eligible used : Finset (Fin q)) : List (Fin q) :=
  (List.finRange q).filter (fun tool => decide (tool ∈ eligible ∧ tool ∉ used))

theorem mem_availableToolList (q : Nat) (eligible used : Finset (Fin q)) (tool : Fin q) :
    tool ∈ availableToolList q eligible used ↔ tool ∈ eligible ∧ tool ∉ used := by
  simp [availableToolList, List.mem_finRange]

theorem availableToolList_eq_nil (q : Nat) (eligible used : Finset (Fin q)) :
    availableToolList q eligible used = [] ↔ eligible ∩ (Finset.univ \ used) = ∅ := by
  constructor
  · intro hnil
    apply Finset.eq_empty_of_forall_notMem
    intro tool htool
    obtain ⟨heligible, hunused⟩ := Finset.mem_inter.mp htool
    have hmem := (mem_availableToolList q eligible used tool).mpr
      ⟨heligible, (Finset.mem_sdiff.mp hunused).2⟩
    rw [hnil] at hmem
    exact List.not_mem_nil hmem
  · intro hempty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro tool htool
    obtain ⟨heligible, hunused⟩ := (mem_availableToolList q eligible used tool).mp htool
    have hmem : tool ∈ eligible ∩ (Finset.univ \ used) :=
      Finset.mem_inter.mpr ⟨heligible, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hunused⟩⟩
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem

/-- Reuses one already constructed capacity table, including for all candidates. -/
def pickMaxRankTool (q : Nat) (table : CapacityTable (Fin q) (q + 1))
    (next : Fin table.rows.size) (eligible used : Finset (Fin q)) : Option (Fin q) :=
  List.argmax (fun tool => table.extractedRank q next (insert tool used))
    (availableToolList q eligible used)

theorem pickMaxRankTool_eq_none (q : Nat) (table : CapacityTable (Fin q) (q + 1))
    (next : Fin table.rows.size) (eligible used : Finset (Fin q)) :
    pickMaxRankTool q table next eligible used = none ↔
      eligible ∩ (Finset.univ \ used) = ∅ := by
  rw [pickMaxRankTool, List.argmax_eq_none, availableToolList_eq_nil]

theorem built_pickMaxRankTool_spec (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1))
    (eligible used : Finset (Fin q)) (tool : Fin q)
    (hpick : pickMaxRankTool q (buildCapacityTable q full (q + 1))
      (builtTableRow q full (q + 1) next) eligible used = some tool) :
    tool ∈ eligible ∧ tool ∉ used ∧
      errorRank (full.drop next.val) ((Finset.univ \ used).erase tool) =
        badChildRank eligible (full.drop next.val) (Finset.univ \ used) := by
  let score := fun candidate => (buildCapacityTable q full (q + 1)).extractedRank q
    (builtTableRow q full (q + 1) next) (insert candidate used)
  change List.argmax score (availableToolList q eligible used) = some tool at hpick
  have hscore (candidate : Fin q) : score candidate =
      errorRank (full.drop next.val) ((Finset.univ \ used).erase candidate) := by
    simpa only [score, remaining_after_used_insert] using
      built_extractedRank_eq_errorRank q full hlaminar next (insert candidate used)
  have hfields := (mem_availableToolList q eligible used tool).mp (List.argmax_mem hpick)
  refine ⟨hfields.1, hfields.2, le_antisymm ?_ ?_⟩
  · apply childRank_le_badChildRank
    exact Finset.mem_inter.mpr ⟨hfields.1,
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hfields.2⟩⟩
  · apply Finset.sup_le
    intro candidate hcandidate
    obtain ⟨heligible, hunused⟩ := Finset.mem_inter.mp hcandidate
    have hmem := (mem_availableToolList q eligible used candidate).mpr
      ⟨heligible, (Finset.mem_sdiff.mp hunused).2⟩
    have hle := List.le_of_mem_argmax hmem hpick
    rw [hscore candidate, hscore tool] at hle
    exact hle

theorem built_pickMaxRankTool_exists (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1))
    (eligible used : Finset (Fin q)) (hnonempty : (eligible ∩ (Finset.univ \ used)).Nonempty) :
    ∃ tool, pickMaxRankTool q (buildCapacityTable q full (q + 1))
      (builtTableRow q full (q + 1) next) eligible used = some tool ∧
      tool ∈ eligible ∧ tool ∉ used ∧
      errorRank (full.drop next.val) ((Finset.univ \ used).erase tool) =
        badChildRank eligible (full.drop next.val) (Finset.univ \ used) := by
  cases hpick : pickMaxRankTool q (buildCapacityTable q full (q + 1))
      (builtTableRow q full (q + 1) next) eligible used with
  | none =>
    have hempty := (pickMaxRankTool_eq_none q _ _ eligible used).mp hpick
    exact False.elim (hnonempty.ne_empty hempty)
  | some tool => exact ⟨tool, rfl, built_pickMaxRankTool_spec q full hlaminar next eligible used tool hpick⟩

/-- The computed maximizing action preserves the required erroneous-child
safety whenever the current live state is safe. -/
theorem built_pickMaxRankTool_safe (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1))
    (eligible used : Finset (Fin q)) (budget : Nat) (tool : Fin q)
    (hpick : pickMaxRankTool q (buildCapacityTable q full (q + 1))
      (builtTableRow q full (q + 1) next) eligible used = some tool)
    (hsafe : Safe (eligible :: full.drop next.val) (Finset.univ \ used) (budget + 1)) :
    Safe (full.drop next.val) ((Finset.univ \ used).erase tool) budget := by
  obtain ⟨_, witness, hwitness, hchild⟩ := (safe_cons_succ_iff _ _ _ _).mp hsafe
  have hbad := (lt_badChildRank_iff eligible (full.drop next.val) (Finset.univ \ used) budget).mpr
    ⟨witness, hwitness, hchild⟩
  apply (safe_iff_lt_errorRank _ _ _).mpr
  rw [(built_pickMaxRankTool_spec q full hlaminar next eligible used tool hpick).2.2]
  exact hbad

theorem built_pickMaxRankTool_safe_exists (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (next : Fin (full.length + 1))
    (eligible used : Finset (Fin q)) (budget : Nat)
    (hsafe : Safe (eligible :: full.drop next.val) (Finset.univ \ used) (budget + 1)) :
    ∃ tool, pickMaxRankTool q (buildCapacityTable q full (q + 1))
      (builtTableRow q full (q + 1) next) eligible used = some tool ∧
      tool ∈ eligible ∧ tool ∉ used ∧
      Safe (full.drop next.val) ((Finset.univ \ used).erase tool) budget := by
  obtain ⟨_, witness, hwitness, _⟩ := (safe_cons_succ_iff _ _ _ _).mp hsafe
  obtain ⟨tool, hpick, heligible, hunused, _⟩ := built_pickMaxRankTool_exists q full hlaminar
    next eligible used ⟨witness, hwitness⟩
  exact ⟨tool, hpick, heligible, hunused,
    built_pickMaxRankTool_safe q full hlaminar next eligible used budget tool hpick hsafe⟩

/-- The successor row and eligible set are those of the original full input. -/
theorem built_pickMaxRankTool_at_stage (q : Nat) (full : List (Finset (Fin q)))
    (hlaminar : LaminarSchedule full) (stage : Fin full.length) (used : Finset (Fin q))
    (budget : Nat)
    (hsafe : Safe (full.drop stage.val) (Finset.univ \ used) (budget + 1)) :
    let next : Fin (full.length + 1) := ⟨stage.val + 1, by omega⟩
    ∃ tool, pickMaxRankTool q (buildCapacityTable q full (q + 1))
      (builtTableRow q full (q + 1) next) full[stage.val] used = some tool ∧
      tool ∈ full[stage.val] ∧ tool ∉ used ∧
      Safe (full.drop (stage.val + 1)) ((Finset.univ \ used).erase tool) budget := by
  rw [List.drop_eq_getElem_cons stage.isLt] at hsafe
  exact built_pickMaxRankTool_safe_exists q full hlaminar ⟨stage.val + 1, by omega⟩
    full[stage.val] used budget hsafe

end PaperProofs.Structure.LaminarTree
