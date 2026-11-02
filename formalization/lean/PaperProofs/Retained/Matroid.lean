module

public import PaperProofs.Retained.Model
public import Mathlib.Combinatorics.Matroid.IndepAxioms

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open Function

namespace PaperProofs.Retained

open Common

variable {I : Instance}

private abbrev Dummy (small large : Finset I.Stage) := {i : I.Stage // i ∈ small \ large}

/-- Dummy labels are solely a Hall-proof device; they are not native tools. -/
private def extendedEligible (small large : Finset I.Stage)
    (i : {i : I.Stage // i ∈ small ∪ large}) : Finset (I.Tool ⊕ Dummy small large) :=
  (I.eligible i.val).image Sum.inl ∪
    if i.val ∈ small then ∅ else Finset.univ.image Sum.inr

private theorem real_mem_extended (small large : Finset I.Stage)
    (i : {i : I.Stage // i ∈ small ∪ large}) (r : I.Tool) :
    Sum.inl r ∈ extendedEligible small large i ↔ r ∈ I.eligible i.val := by
  unfold extendedEligible
  split_ifs <;> simp

private theorem dummy_mem_extended (small large : Finset I.Stage)
    (i : {i : I.Stage // i ∈ small ∪ large}) (hi : i.val ∉ small)
    (d : Dummy small large) : Sum.inr d ∈ extendedEligible small large i := by
  simp [extendedEligible, hi]

private theorem dummy_not_mem_extended (small large : Finset I.Stage)
    (i : {i : I.Stage // i ∈ small ∪ large}) (hi : i.val ∈ small)
    (d : Dummy small large) : Sum.inr d ∉ extendedEligible small large i := by
  simp [extendedEligible, hi]

private theorem extended_hall {small large : Finset I.Stage}
    (hsmall : Matchable I small) (hlarge : Matchable I large) :
    ∀ s : Finset {i : I.Stage // i ∈ small ∪ large},
      s.card ≤ (s.biUnion (extendedEligible small large)).card := by
  classical
  rcases hsmall with ⟨fsmall, hsmallInj, hsmallComp⟩
  rcases hlarge with ⟨flarge, hlargeInj, hlargeComp⟩
  intro s
  have hcardOf (g : s → I.Tool ⊕ Dummy small large) (hg : Injective g)
      (hmem : ∀ i, g i ∈ s.biUnion (extendedEligible small large)) :
      s.card ≤ (s.biUnion (extendedEligible small large)).card := by
    let assignment : s → {r // r ∈ s.biUnion (extendedEligible small large)} :=
      fun i => ⟨g i, hmem i⟩
    have hinj : Injective assignment := by
      intro i j hij
      exact hg (congrArg Subtype.val hij)
    simpa only [Fintype.card_coe] using Fintype.card_le_of_injective assignment hinj
  by_cases hallSmall : ∀ i ∈ s, i.val ∈ small
  · let g : s → I.Tool ⊕ Dummy small large :=
      fun i => Sum.inl (fsmall ⟨i.val.val, hallSmall i.val i.property⟩)
    apply hcardOf g
    · intro i j hij
      have htools : fsmall ⟨i.val.val, hallSmall i.val i.property⟩ =
          fsmall ⟨j.val.val, hallSmall j.val j.property⟩ := Sum.inl.inj hij
      have hstage : i.val.val = j.val.val :=
        congrArg (fun z : {i : I.Stage // i ∈ small} => z.val) (hsmallInj htools)
      apply Subtype.ext
      apply Subtype.ext
      exact hstage
    · intro i
      exact Finset.mem_biUnion.mpr ⟨i.val, i.property,
        (real_mem_extended small large i.val _).mpr (hsmallComp _)⟩
  · have hcounter : ∃ i ∈ s, i.val ∉ small := by
      simpa only [not_forall, not_imp, exists_prop] using hallSmall
    obtain ⟨i0, hi0, hi0small⟩ := hcounter
    let dummyFor (i : s) (hnot : i.val.val ∉ large) : Dummy small large :=
      ⟨i.val.val, Finset.mem_sdiff.mpr
        ⟨(Finset.mem_union.mp i.val.property).resolve_right hnot, hnot⟩⟩
    let g : s → I.Tool ⊕ Dummy small large := fun i =>
      if hi : i.val.val ∈ large then Sum.inl (flarge ⟨i.val.val, hi⟩)
      else Sum.inr (dummyFor i hi)
    apply hcardOf g
    · intro i j hij
      by_cases hi : i.val.val ∈ large
      · by_cases hj : j.val.val ∈ large
        · have htools : flarge ⟨i.val.val, hi⟩ = flarge ⟨j.val.val, hj⟩ :=
            Sum.inl.inj (by simpa only [g, dite_eq_left hi, dite_eq_left hj] using hij)
          have hstage : i.val.val = j.val.val :=
            congrArg (fun z : {i : I.Stage // i ∈ large} => z.val) (hlargeInj htools)
          apply Subtype.ext
          apply Subtype.ext
          exact hstage
        · simp [g, hi, hj] at hij
      · by_cases hj : j.val.val ∈ large
        · simp [g, hi, hj] at hij
        · have hdummy : dummyFor i hi = dummyFor j hj :=
            Sum.inr.inj (by simpa only [g, dite_eq_right hi, dite_eq_right hj] using hij)
          have hstage : i.val.val = j.val.val :=
            congrArg (fun z : Dummy small large => z.val) hdummy
          apply Subtype.ext
          apply Subtype.ext
          exact hstage
    · intro i
      by_cases hi : i.val.val ∈ large
      · have hm : Sum.inl (flarge ⟨i.val.val, hi⟩) ∈
          s.biUnion (extendedEligible small large) :=
          Finset.mem_biUnion.mpr ⟨i.val, i.property,
            (real_mem_extended small large i.val _).mpr (hlargeComp _)⟩
        simpa only [g, dite_eq_left hi] using hm
      · have hm : Sum.inr (dummyFor i hi) ∈ s.biUnion (extendedEligible small large) :=
          Finset.mem_biUnion.mpr ⟨i0, hi0,
            dummy_mem_extended small large i0 hi0small (dummyFor i hi)⟩
        simpa only [g, dite_eq_right hi] using hm

private theorem exists_extended_matching {small large : Finset I.Stage}
    (hsmall : Matchable I small) (hlarge : Matchable I large) :
    ∃ f : {i : I.Stage // i ∈ small ∪ large} → I.Tool ⊕ Dummy small large,
      Injective f ∧ ∀ i, f i ∈ extendedEligible small large i :=
  (Finset.all_card_le_biUnion_card_iff_existsInjective'
    (extendedEligible small large)).mp (extended_hall hsmall hlarge)

/-- Genuine finite exchange for distinct-compatible matchability. The Hall
construction's auxiliary labels are discarded before returning this witness. -/
theorem matchingAugmentation (I : Instance) : MatchingAugmentation I := by
  classical
  intro small large hsmall hlarge hcard
  obtain ⟨f, hfinj, hfcomp⟩ := exists_extended_matching hsmall hlarge
  let toUnion : {i : I.Stage // i ∈ large \ small} →
      {i : I.Stage // i ∈ small ∪ large} := fun i =>
    ⟨i.val, Finset.mem_union_right small (Finset.mem_sdiff.mp i.property).1⟩
  have hreal : ∃ i : {i : I.Stage // i ∈ large \ small},
      ∃ r : I.Tool, f (toUnion i) = Sum.inl r := by
    by_contra hnone
    have hright (i : {i : I.Stage // i ∈ large \ small}) :
        ∃ d : Dummy small large, f (toUnion i) = Sum.inr d := by
      cases hvalue : f (toUnion i) with
      | inl r => exact False.elim (hnone ⟨i, r, hvalue⟩)
      | inr d => exact ⟨d, rfl⟩
    let d : {i : I.Stage // i ∈ large \ small} → Dummy small large :=
      fun i => Classical.choose (hright i)
    have hd (i : {i : I.Stage // i ∈ large \ small}) : f (toUnion i) = Sum.inr (d i) :=
      Classical.choose_spec (hright i)
    have hdinj : Injective d := by
      intro i j hij
      have hf : f (toUnion i) = f (toUnion j) := by rw [hd i, hd j, hij]
      have hstage : i.val = j.val :=
        congrArg (fun z : {i : I.Stage // i ∈ small ∪ large} => z.val) (hfinj hf)
      exact Subtype.ext hstage
    have hdiff : (large \ small).card ≤ (small \ large).card := by
      simpa only [Dummy, Fintype.card_coe] using Fintype.card_le_of_injective d hdinj
    have hsmallCard := Finset.card_sdiff_add_card_inter small large
    have hlargeCard := Finset.card_sdiff_add_card_inter large small
    rw [Finset.inter_comm large small] at hlargeCard
    omega
  obtain ⟨extra, r0, hextra⟩ := hreal
  refine ⟨extra.val, extra.property, ?_⟩
  let toUnion' : {i : I.Stage // i ∈ insert extra.val small} →
      {i : I.Stage // i ∈ small ∪ large} := fun i =>
    ⟨i.val, by
      rcases Finset.mem_insert.mp i.property with hsame | hmem
      · rw [hsame]
        exact Finset.mem_union_right small (Finset.mem_sdiff.mp extra.property).1
      · exact Finset.mem_union_left large hmem⟩
  have hleft (i : {i : I.Stage // i ∈ insert extra.val small}) :
      ∃ r : I.Tool, f (toUnion' i) = Sum.inl r := by
    by_cases hi : i.val ∈ small
    · have hno (d : Dummy small large) : f (toUnion' i) ≠ Sum.inr d := by
        intro heq
        have hmem := hfcomp (toUnion' i)
        rw [heq] at hmem
        exact dummy_not_mem_extended small large (toUnion' i) hi d hmem
      cases hvalue : f (toUnion' i) with
      | inl r => exact ⟨r, rfl⟩
      | inr d => exact False.elim (hno d hvalue)
    · have hieq : i.val = extra.val := (Finset.mem_insert.mp i.property).resolve_right hi
      have hunion : toUnion' i = toUnion extra := Subtype.ext hieq
      exact ⟨r0, by rw [hunion]; exact hextra⟩
  let assignment : {i : I.Stage // i ∈ insert extra.val small} → I.Tool :=
    fun i => Classical.choose (hleft i)
  have hassignment (i : {i : I.Stage // i ∈ insert extra.val small}) :
      f (toUnion' i) = Sum.inl (assignment i) :=
    Classical.choose_spec (hleft i)
  refine ⟨assignment, ?_, ?_⟩
  · intro i j hij
    have hf : f (toUnion' i) = f (toUnion' j) := by
      rw [hassignment i, hassignment j, hij]
    have hstage : i.val = j.val :=
      congrArg (fun z : {i : I.Stage // i ∈ small ∪ large} => z.val) (hfinj hf)
    exact Subtype.ext hstage
  · intro i
    have hmem := hfcomp (toUnion' i)
    rw [hassignment i] at hmem
    exact (real_mem_extended small large (toUnion' i) (assignment i)).mp hmem

noncomputable def transversalIndependence (I : Instance) : IndepMatroid I.Stage :=
  IndepMatroid.ofFinset Set.univ (Matchable I) (matchable_empty I)
    (by intro small large hlarge hsub; exact hlarge.subset hsub)
    (by
      intro small large hsmall hlarge hcard
      obtain ⟨i, hi, hmatch⟩ := matchingAugmentation I small large hsmall hlarge hcard
      exact ⟨i, (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2, hmatch⟩)
    (by intro errors _; exact Set.subset_univ _)

/-- The actual transversal matroid, constructed from the proved finite Hall
augmentation theorem rather than supplied as an input assumption. -/
noncomputable def transversalMatroid (I : Instance) : Matroid I.Stage :=
  (transversalIndependence I).matroid

theorem transversalMatroid_ground (I : Instance) : (transversalMatroid I).E = Set.univ := by
  simp only [transversalMatroid, IndepMatroid.matroid_E,
    transversalIndependence, IndepMatroid.ofFinset_E]

theorem transversalMatroid_indep (I : Instance) (errors : Finset I.Stage) :
    (transversalMatroid I).Indep (errors : Set I.Stage) ↔ Matchable I errors := by
  simp only [transversalMatroid, IndepMatroid.matroid_indep_iff,
    transversalIndependence, IndepMatroid.ofFinset_indep]

theorem transversalMatroidCorrespondence (I : Instance) : TransversalMatroidCorrespondence I :=
  ⟨transversalMatroid I, transversalMatroid_ground I, transversalMatroid_indep I⟩

/-- The finite minimal-unmatchable circuits are precisely the circuits of
the constructed Mathlib matroid. No representation property is assumed. -/
theorem transversalMatroid_circuit (I : Instance) (errors : Finset I.Stage) :
    (transversalMatroid I).IsCircuit (errors : Set I.Stage) ↔ Circuit I errors := by
  classical
  constructor
  · intro hcircuit
    refine ⟨?_, ?_⟩
    · intro hmatch
      exact hcircuit.not_indep ((transversalMatroid_indep I errors).mpr hmatch)
    · intro smaller hproper
      exact (transversalMatroid_indep I smaller).mp
        (hcircuit.ssubset_indep (Finset.coe_ssubset.mpr hproper))
  · intro hcircuit
    apply Matroid.isCircuit_iff_forall_ssubset.mpr
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro hindep
      exact hcircuit.1 ((transversalMatroid_indep I errors).mp hindep)
    · rw [transversalMatroid_ground]
      exact Set.subset_univ _
    · intro subset hproper
      have hfinite : subset.Finite := Set.toFinite subset
      have hproper' : hfinite.toFinset ⊂ errors := by
        apply Finset.coe_ssubset.mp
        simpa only [Set.Finite.coe_toFinset] using hproper
      have hmatch := hcircuit.2 hfinite.toFinset hproper'
      have hindep := (transversalMatroid_indep I hfinite.toFinset).mpr hmatch
      simpa only [Set.Finite.coe_toFinset] using hindep

end PaperProofs.Retained
