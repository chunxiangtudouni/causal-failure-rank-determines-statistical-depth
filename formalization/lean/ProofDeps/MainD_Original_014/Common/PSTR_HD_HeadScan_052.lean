module

public import Common.PSTR_HD_TableHeads_002

/-! Exact original critical-index predicate for a real encoded-rank scan.
These are specifications, never runtime query/bitmap/rank input fields. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims

theorem encodeRank_nat (q value : Nat) : encodeRank q (value : ℕ∞) = value := by
  simp [encodeRank]

theorem encoded_lt_sentinel (q : Nat) (rank : ℕ∞) (hfinite : rank ≠ ⊤)
    (hbound : rank ≤ ((q + 1 : Nat) : ℕ∞)) : encodeRank q rank < q + 2 := by
  obtain ⟨value, hv⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hb : value ≤ q + 1 := ENat.natCast_le_natCast.mp (hv.symm ▸ hbound)
  rw [← hv, encodeRank_nat]
  omega

theorem encoded_bound (q : Nat) (rank : ℕ∞)
    (hbound : rank ≠ ⊤ → rank ≤ ((q + 1 : Nat) : ℕ∞)) : encodeRank q rank ≤ q + 2 := by
  by_cases ht : rank = ⊤
  · simp [encodeRank, ht]
  · exact (encoded_lt_sentinel q rank ht (hbound ht)).le

theorem encoded_sentinel_iff (q : Nat) (rank : ℕ∞)
    (hbound : rank ≠ ⊤ → rank ≤ ((q + 1 : Nat) : ℕ∞)) :
    encodeRank q rank = q + 2 ↔ rank = ⊤ := by
  by_cases ht : rank = ⊤
  · simp [encodeRank, ht]
  · have hs := encoded_lt_sentinel q rank ht (hbound ht)
    exact ⟨fun he => False.elim (by omega), fun he => False.elim (ht he)⟩

theorem encoded_successor_iff (q : Nat) (rank bad : ℕ∞) (hfinite : rank ≠ ⊤)
    (hbound : rank ≤ ((q + 1 : Nat) : ℕ∞)) :
    encodeRank q bad + 1 = encodeRank q rank ↔ bad + 1 = rank := by
  obtain ⟨value, hv⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hb : value ≤ q + 1 := ENat.natCast_le_natCast.mp (hv.symm ▸ hbound)
  by_cases ht : bad = ⊤
  · rw [ht, ← hv, encodeRank_nat]
    simp only [encodeRank, ↓reduceIte, top_add, ENat.top_ne_natCast, iff_false]
    omega
  · obtain ⟨b, he⟩ := ENat.ne_top_iff_exists.mp ht
    rw [← hv, ← he, encodeRank_nat, encodeRank_nat]
    change b + 1 = value ↔ ((b + 1 : Nat) : ℕ∞) = (value : ℕ∞)
    exact ENat.natCast_inj.symm

def headGate (q rank bad : Nat) : Bool := decide (rank < q + 2 ∧ bad + 1 = rank)

theorem headGate_correct (q : Nat) (rank bad : ℕ∞)
    (hbound : rank ≠ ⊤ → rank ≤ ((q + 1 : Nat) : ℕ∞)) :
    headGate q (encodeRank q rank) (encodeRank q bad) = true ↔ rank ≠ ⊤ ∧ bad + 1 = rank := by
  simp only [headGate, decide_eq_true_eq]
  constructor
  · rintro ⟨hr, he⟩
    have hf : rank ≠ ⊤ := by intro ht; simp [encodeRank, ht] at hr
    exact ⟨hf, (encoded_successor_iff q rank bad hf (hbound hf)).mp he⟩
  · rintro ⟨hf, he⟩
    exact ⟨encoded_lt_sentinel q rank hf (hbound hf), (encoded_successor_iff q rank bad hf (hbound hf)).mpr he⟩

noncomputable def initialRank (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) : ℕ∞ :=
  (callback q full ⟨0, by omega⟩ used).rank

noncomputable def badAt (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (stage : Fin full.length) : ℕ∞ :=
  (callback q full ⟨stage.val, by have := stage.isLt; omega⟩ used).bad

theorem initial_finite_bound (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (hf : initialRank q full used ≠ ⊤) :
    initialRank q full used ≤ ((q + 1 : Nat) : ℕ∞) := by
  have he : initialRank q full used = errorRank full (Finset.univ \ used) := by
    simpa only [initialRank, List.drop_zero] using PSTRCallback.callback_rank q full hl ⟨0, by omega⟩ used
  rw [he] at hf ⊢
  exact IndexedQuery.errorRank_finite_le_q_add_one q full (Finset.univ \ used) hf

theorem initial_encoded_bound (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) : encodeRank q (initialRank q full used) ≤ q + 2 :=
  encoded_bound q _ (initial_finite_bound q full hl used)

theorem bad_encoded_bound (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (stage : Fin full.length) : encodeRank q (badAt q full used stage) ≤ q + 2 := by
  apply encoded_bound
  intro hf
  have he : badAt q full used stage = badChildRank full[stage.val] (full.drop (stage.val + 1)) (Finset.univ \ used) :=
    (PSTRCallback.callback_stage q full hl stage used).2.1
  rw [he] at hf ⊢
  exact IndexedQuery.badChildRank_finite_le_q_add_one q _ _ _ hf

noncomputable def headAt (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (stage : Nat) : Bool :=
  if hstage : stage < full.length then
    headGate q (encodeRank q (initialRank q full used)) (encodeRank q (badAt q full used ⟨stage, hstage⟩))
  else false

theorem headAt_correct (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (stage : Fin full.length) :
    headAt q full used stage.val = true ↔ initialRank q full used ≠ ⊤ ∧ badAt q full used stage + 1 = initialRank q full used := by
  rw [headAt, dite_eq_left stage.isLt]
  exact headGate_correct q _ _ (initial_finite_bound q full hl used)

noncomputable def scanPrefix (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (count : Nat) : List Nat :=
  (List.range count).filter (headAt q full used)

theorem scanPrefix_zero (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    scanPrefix q full used 0 = [] := rfl

theorem scanPrefix_succ (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (count : Nat) :
    scanPrefix q full used (count + 1) = scanPrefix q full used count ++
      (if headAt q full used count then [count] else []) := by
  simp only [scanPrefix, List.range_succ, List.filter_append, List.filter_cons, List.filter_nil]

theorem scanPrefix_length_le (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (count : Nat) :
    (scanPrefix q full used count).length ≤ count := by
  exact (List.length_filter_le _ _).trans_eq List.length_range

theorem scanPrefix_mem_lt (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (count index : Nat)
    (hi : index ∈ scanPrefix q full used count) : index < count :=
  List.mem_range.mp (List.mem_filter.mp hi).1

theorem finRange_val (size : Nat) : (List.finRange size).map Fin.val = List.range size := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range]
  · intro index hleft hright
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
    rfl

theorem fin_filter_val (size : Nat) (test : Nat → Bool) :
    ((List.finRange size).filter (fun stage => test stage.val)).map Fin.val = (List.range size).filter test := by
  rw [← finRange_val size, List.filter_map]
  simp only [Function.comp_def]

theorem criticalIndices_scan (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full) (used : Finset (Fin q)) :
    criticalIndices q full used = scanPrefix q full used full.length := by
  have he : criticalIndices q full used =
      ((List.finRange full.length).filter (fun stage =>
        decide (initialRank q full used ≠ ⊤ ∧ badAt q full used stage + 1 = initialRank q full used))).map Fin.val := by
    change (if initialRank q full used = ⊤ then [] else
      ((List.finRange full.length).filter (fun stage => decide (badAt q full used stage + 1 = initialRank q full used))).map Fin.val) = _
    by_cases ht : initialRank q full used = ⊤ <;> simp [ht]
  rw [he]
  calc
    _ = ((List.finRange full.length).filter (fun stage => headAt q full used stage.val)).map Fin.val := by
      apply congrArg (List.map Fin.val)
      apply List.filter_congr
      intro stage _
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using (headAt_correct q full hl used stage).symm
    _ = scanPrefix q full used full.length := fin_filter_val full.length (headAt q full used)

theorem headWords_scan (q : Nat) (full : List (Finset (Fin q))) (hl : LaminarSchedule full) (used : Finset (Fin q)) :
    headWords q full used = [encodeRank q (initialRank q full used), (scanPrefix q full used full.length).length] ++
      scanPrefix q full used full.length := by
  simp only [headWords, initialRank, criticalIndices_scan q full hl used]

end PaperProofs.Common.Native.CompactPrice.PSTRHeadScan
