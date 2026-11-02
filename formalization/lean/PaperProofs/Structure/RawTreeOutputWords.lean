module

public import PaperProofs.Structure.RawTreeSerialization

/-! Word-value safety of the original given-tree ROM and its exact
serialization.  This proves no constructor or runtime claim. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawTreeOutputWords

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  RawTreeSerialization

theorem incidence_word_le_one (q : Nat) (supports : List (Finset (Fin q)))
    (value : Nat) (hvalue : value ∈ incidence supports) : value ≤ 1 := by
  obtain ⟨support, _hmem, hvalue⟩ := List.mem_flatMap.mp hvalue
  obtain ⟨tool, _htool, rfl⟩ := List.mem_map.mp hvalue
  simp only [bit]
  split_ifs <;> omega

theorem prepared_child_size_le (q : Nat) (full : List (Finset (Fin q)))
    (parent : (prepareNormalization q full).indexed.NodeId) :
    ((prepareNormalization q full).indexed.children.get parent).size ≤
      (prepareNormalization q full).indexed.nodes.size := by
  rw [indexed_child_size_eq_fiber (prepareNormalization q full).indexed
    (fun parent => indexNodes_children_nodup _ _ parent)
    (fun child parent => indexNodes_child_mem _ _ child parent) parent]
  simpa only [Fintype.card_fin] using Finset.card_le_univ
    ((Finset.univ : Finset (prepareNormalization q full).indexed.NodeId).filter
      (fun child => (prepareNormalization q full).indexed.parents.get child = some parent))

/-- Headers, incidence bits, parent encodings, degrees, and actual child IDs
are all bounded by the original dimension bound.  Laminarity is unnecessary
for this numeric fact about the constructed finite cache. -/
theorem givenTreeROM_word_le (q : Nat) (full : List (Finset (Fin q)))
    (region : Region) (value : Nat) (hvalue : value ∈ (givenTreeROM q full).words region) :
    value ≤ full.length + q + 1 := by
  have ht := prepared_indexed_size_le q full
  cases region with
  | input =>
    change value ∈ (givenTreeROM q full).input at hvalue
    simp only [givenTreeROM, UniformTreeMetadataRAM.nodeRows_eq_incidence,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvalue
    rcases hvalue with ((rfl | rfl | rfl) | hbits) | hnodebits
    · omega
    · omega
    · exact ht
    · exact (incidence_word_le_one q full value hbits).trans (by omega)
    · exact (incidence_word_le_one q (prepareNormalization q full).indexed.nodes.toList
        value hnodebits).trans (by omega)
  | internal =>
    change value ∈ (givenTreeROM q full).internal at hvalue
    simp only [givenTreeROM, List.mem_append] at hvalue
    rcases hvalue with hparent | hdegree
    · obtain ⟨node, _hnode, rfl⟩ := List.mem_map.mp hparent
      exact (UniformNormalizationRAM.encodedNode_le (prepareNormalization q full).indexed
        ((prepareNormalization q full).indexed.parents.get node)).trans ht
    · obtain ⟨node, _hnode, rfl⟩ := List.mem_map.mp hdegree
      exact (prepared_child_size_le q full node).trans ht
  | children =>
    change value ∈ (givenTreeROM q full).children at hvalue
    obtain ⟨parent, _hparent, hchild⟩ := List.mem_flatMap.mp hvalue
    obtain ⟨child, _hchild, rfl⟩ := List.mem_map.mp hchild
    exact child.isLt.le.trans ht

theorem givenTreeROM_wordsFit (q : Nat) (full : List (Finset (Fin q))) :
    ∀ region, WordsFit (indexWidth 16 full.length q) ((givenTreeROM q full).words region) := by
  intro region value hvalue
  have hbound := givenTreeROM_word_le q full region value hvalue
  exact lt_of_le_of_lt (hbound.trans (by omega : full.length + q + 1 ≤
    full.length * q + full.length + q + 640)) (fits_checker_register_bound full.length q)

theorem serialize_givenTreeROM_wordsFit (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    WordsFit (indexWidth 16 full.length q) (serializeROM (givenTreeROM q full)) := by
  have hlength := serialize_givenTreeROM_length_fits q full hq hlaminar
  have hlen := serializeROM_length (givenTreeROM q full)
  intro value hvalue
  simp only [serializeROM, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hvalue
  rcases hvalue with (((rfl | rfl | rfl) | hin) | hint) | hchild
  · exact lt_of_le_of_lt (by rw [hlen, PhysicalROM.size]; omega) hlength
  · exact lt_of_le_of_lt (by rw [hlen, PhysicalROM.size]; omega) hlength
  · exact lt_of_le_of_lt (by rw [hlen, PhysicalROM.size]; omega) hlength
  · exact givenTreeROM_wordsFit q full .input value hin
  · exact givenTreeROM_wordsFit q full .internal value hint
  · exact givenTreeROM_wordsFit q full .children value hchild

end PaperProofs.Structure.LaminarTree.RawTreeOutputWords
