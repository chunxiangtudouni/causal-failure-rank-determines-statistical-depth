module

public import PaperProofs.Structure.CompactControllerClaims

/-! The original table-tie callback, independently of the generic tool tie.
No machine or statistical performance premise is used. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCallback

universe u

open AlgorithmClaims CompactControllerClaims

theorem zero_remaining (used : Finset (Fin 0)) : Finset.univ \ used = ∅ := by
  exact Finset.eq_empty_of_forall_notMem (fun tool _ => Fin.elim0 tool)

theorem zero_rank (full : List (Finset (Fin 0))) (offset : Nat) (used : Finset (Fin 0)) :
    errorRank (full.drop offset) (Finset.univ \ used) =
      if offset < full.length then 1 else ⊤ := by
  rw [zero_remaining]
  split_ifs with h
  · rw [List.drop_eq_getElem_cons h, errorRank_no_tools]
  · rw [List.drop_eq_nil_of_le (by omega), errorRank_terminal]

theorem callback_rank (q : Nat) (full : List (Finset (Fin q)))
    (hl : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q)) :
    (callback q full stage used).rank = errorRank (full.drop stage.val) (Finset.univ \ used) := by
  by_cases hq : 0 < q
  · simpa only [callback, hq, ↓reduceDIte] using expectedReply_rank q full hq hl stage used
  · have hz : q = 0 := by omega
    subst q
    simpa only [callback, Nat.lt_irrefl, ↓reduceDIte] using (zero_rank full stage.val used).symm

theorem callback_stage (q : Nat) (full : List (Finset (Fin q)))
    (hl : LaminarSchedule full) (stage : Fin full.length) (used : Finset (Fin q)) :
    let reply := callback q full ⟨stage.val, by omega⟩ used
    reply.good = errorRank (full.drop (stage.val + 1)) (Finset.univ \ used) ∧
    reply.bad = badChildRank full[stage.val] (full.drop (stage.val + 1)) (Finset.univ \ used) ∧
    (reply.tool = none ↔ full[stage.val] ∩ (Finset.univ \ used) = ∅) ∧
    (∀ tool, reply.tool = some tool → tool ∈ full[stage.val] ∧ tool ∉ used ∧
      errorRank (full.drop (stage.val + 1)) ((Finset.univ \ used).erase tool) = reply.bad) := by
  by_cases hq : 0 < q
  · simp only [callback, hq, ↓reduceDIte, expectedReply, stage.isLt]
    have hg := IndexedQuery.stored_query_good q full hq hl used stage
    have hb := IndexedQuery.stored_query_bad q full hq hl used stage
    have hn := IndexedQuery.stored_query_tool_none_iff q full hq hl used stage
    refine ⟨hg, hb, hn, ?_⟩
    intro tool hpick
    obtain ⟨he, hu, hr⟩ := IndexedQuery.stored_query_tool_spec q full hq hl used stage tool hpick
    exact ⟨he, hu, hr.trans hb.symm⟩
  · have hz : q = 0 := by omega
    subst q
    dsimp only
    simp only [callback, Nat.lt_irrefl, ↓reduceDIte]
    refine ⟨(zero_rank full (stage.val + 1) used).symm, ?_, ?_, ?_⟩
    · simp [badChildRank]
    · simp
    · intro tool
      exact Fin.elim0 tool

theorem callbackPlan_safe (q : Nat) (full : List (Finset (Fin q)))
    (hl : LaminarSchedule full) (suffix : List (Finset (Fin q)))
    (offset : Nat) (hdrop : suffix = full.drop offset) (used : Finset (Fin q)) (budget : Nat)
    (hsafe : Safe suffix (Finset.univ \ used) budget) :
    SafePlan (callbackPlan q full suffix offset used) (Finset.univ \ used) budget := by
  induction suffix generalizing offset used budget with
  | nil =>
    intro errors herr play
    cases play
  | cons eligible later ih =>
    cases budget with
    | zero => exact safePlan_zero _ _
    | succ budget =>
      have htail : later = full.drop (offset + 1) := by
        have h := congrArg List.tail hdrop
        simpa only [List.tail_cons, List.tail_drop] using h
      have hoffset : offset < full.length := by
        by_contra h
        have hempty := List.drop_eq_nil_of_le (show full.length ≤ offset by omega)
        rw [← hdrop] at hempty
        exact List.cons_ne_nil _ _ hempty
      have he : eligible = full[offset] := by
        rw [List.drop_eq_getElem_cons hoffset] at hdrop
        exact (List.cons.inj hdrop).1
      have hoffset' : offset < full.length + 1 := by omega
      obtain ⟨hg, witness, hw, hchild⟩ := (safe_cons_succ_iff _ _ _ _).mp hsafe
      have hnonempty : eligible ∩ (Finset.univ \ used) ≠ ∅ :=
        Finset.nonempty_iff_ne_empty.mp ⟨witness, hw⟩
      have spec := callback_stage q full hl ⟨offset, hoffset⟩ used
      dsimp only at spec
      cases hpick : (callback q full ⟨offset, hoffset'⟩ used).tool with
      | none => exact (hnonempty (he.symm ▸ spec.2.2.1.mp hpick)).elim
      | some tool =>
        obtain ⟨heligible, hunused, hmax⟩ := spec.2.2.2 tool hpick
        have hbad : Safe later ((Finset.univ \ used).erase tool) budget := by
          apply (safe_iff_lt_errorRank _ _ _).mpr
          rw [htail, hmax, spec.2.1, ← he]
          exact (lt_badChildRank_iff _ _ _ budget).mpr ⟨witness, hw, htail ▸ hchild⟩
        have hgPlan := ih (offset + 1) htail used (budget + 1) hg
        have hbPlan := ih (offset + 1) htail (insert tool used) budget
          (by simpa only [remaining_after_used_insert] using hbad)
        simp only [callbackPlan, hoffset', ↓reduceDIte, hpick]
        apply safePlan_choose_of _ _ _ budget tool hgPlan
        · exact Finset.mem_inter.mpr ⟨he.symm ▸ heligible,
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hunused⟩⟩
        · simpa only [remaining_after_used_insert] using hbPlan

theorem callbackClaims : CallbackClaims := by
  intro q full hl
  refine ⟨callback_rank q full hl, callback_stage q full hl, ?_⟩
  intro offset used budget
  constructor
  · exact fun hp => ⟨_, hp⟩
  · exact callbackPlan_safe q full hl _ offset.val rfl used budget

open PaperProofs.Common PaperProofs.Common.Native

theorem native_remaining (I : Instance) (available : Finset I.Tool)
    (history : List (VisibleEvent I)) :
    Finset.univ \ nativeExcluded I available history = available \ historyUsed history := by
  ext tool
  simp only [nativeExcluded, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  tauto

theorem nativeCallbackClaims : NativeCallbackClaims.{u} := by
  intro I hl available input C mode accounting Seed policy seed truth tapes n state hp stage hs
  have hc : historyCursor state.history = stage.val :=
    (prefix_historyCursor input C mode accounting policy seed truth tapes hp).trans hs
  have hc' : historyCursor state.history < I.compatibility.length + 1 := by
    rw [hc]
    exact Nat.lt_succ_of_lt stage.isLt
  let cursor : Fin (I.compatibility.length + 1) := ⟨stage.val, by omega⟩
  let used := nativeExcluded I available state.history
  let reply := callback I.toolCount I.compatibility cursor used
  have spec := callback_stage I.toolCount I.compatibility hl stage used
  dsimp only at spec
  have hrem := native_remaining I available state.history
  have hr := callback_rank I.toolCount I.compatibility hl cursor used
  refine ⟨reply, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nativeReply, dite_eq_left hc']
    have hfin : (⟨historyCursor state.history, hc'⟩ : Fin (I.compatibility.length + 1)) = cursor :=
      Fin.ext hc
    rw [hfin]
  · rw [hrem, prefix_historyUsed input C mode accounting policy seed truth tapes hp] at hr
    exact hr
  · simpa only [used, hrem] using spec.1
  · simpa only [used, hrem, Instance.eligible, List.get_eq_getElem] using spec.2.1
  · simpa only [used, hrem, Instance.eligible, List.get_eq_getElem] using spec.2.2.1
  · intro tool ht
    obtain ⟨he, hu, hm⟩ := spec.2.2.2 tool ht
    have hmem : tool ∈ available \ historyUsed state.history := by
      rw [← hrem]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩
    obtain ⟨ha, hh⟩ := Finset.mem_sdiff.mp hmem
    refine ⟨ha, he, hh, ?_, ?_⟩
    · simpa only [used, hrem] using hm
    · intro handle hstage active valid unallocated window resources
      apply Step.allocate state handle tool active valid
      · simpa only [hstage, Instance.eligible, List.get_eq_getElem] using he
      · exact (prefix_historyUnused_iff input C mode accounting policy seed truth tapes hp tool).mp hh
      · exact unallocated
      · exact window
      · exact resources

end PaperProofs.Structure.LaminarTree.PSTRCallback
