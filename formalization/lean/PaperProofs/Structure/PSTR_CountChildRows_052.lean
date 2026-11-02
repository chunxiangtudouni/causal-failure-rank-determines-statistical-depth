module

public import PaperProofs.Structure.PSTR_HD_StaticLayout_019

/-! The outer loop's flat-child offset is the length of preceding real
rows in ORIGINAL staticMetadata. These proof specifications are not runtime
ROM fields. The advance code must maintain the offset by actual degree adds. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountChildRows

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def rows {q : Nat} (full : List (Finset (Fin q))) : List (List Nat) :=
  (List.finRange (prepareNormalization q full).indexed.nodes.size).map
    (fun node => ((prepareNormalization q full).indexed.children.get node).toList.map Fin.val)

def flatOffset {q : Nat} (full : List (Finset (Fin q))) (node : Nat) : Nat :=
  ((rows full).take node).flatten.length

theorem rows_length {q : Nat} (full : List (Finset (Fin q))) :
    (rows full).length = (prepareNormalization q full).indexed.nodes.size := by simp [rows]

theorem row_get {q : Nat} (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    (rows full)[node.val]'(by rw [rows_length]; exact node.isLt) =
      ((prepareNormalization q full).indexed.children.get node).toList.map Fin.val := by
  simp only [rows, List.getElem_map, List.getElem_finRange]
  rfl

theorem childWords_eq {q : Nat} (full : List (Finset (Fin q))) :
    PSTRStaticLayout.childWords q full = (rows full).flatten := rfl

theorem offset_zero {q : Nat} (full : List (Finset (Fin q))) : flatOffset full 0 = 0 := rfl

theorem offset_succ {q : Nat} (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    flatOffset full (node.val + 1) = flatOffset full node.val +
      ((prepareNormalization q full).indexed.children.get node).size := by
  unfold flatOffset
  rw [List.take_succ_eq_append_getElem (by rw [rows_length]; exact node.isLt),
    List.flatten_append, List.length_append, row_get]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.length_map, Array.length_toList]

theorem offset_end {q : Nat} (full : List (Finset (Fin q))) :
    flatOffset full (prepareNormalization q full).indexed.nodes.size = PSTRStaticLayout.edgeCount q full := by
  unfold flatOffset PSTRStaticLayout.edgeCount
  rw [childWords_eq, List.take_of_length_le (by rw [rows_length])]

theorem offset_le {q : Nat} (full : List (Finset (Fin q))) (node : Nat) :
    flatOffset full node ≤ PSTRStaticLayout.edgeCount q full := by
  have he : ((rows full).take node).flatten ++ ((rows full).drop node).flatten =
      PSTRStaticLayout.childWords q full := by
    rw [← List.flatten_append, List.take_append_drop, childWords_eq]
  have hl := congrArg List.length he
  simp only [List.length_append] at hl
  unfold flatOffset PSTRStaticLayout.edgeCount
  omega

theorem row_bound {q : Nat} (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    flatOffset full node.val + ((prepareNormalization q full).indexed.children.get node).size ≤
      PSTRStaticLayout.edgeCount q full := by
  rw [← offset_succ]
  exact offset_le full (node.val + 1)

theorem row_alignment {q : Nat} (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) (position : Nat)
    (hp : position < ((prepareNormalization q full).indexed.children.get node).size) :
    (PSTRStaticLayout.childWords q full).getD (flatOffset full node.val + position) 0 =
      (((prepareNormalization q full).indexed.children.get node)[position]).val := by
  rw [childWords_eq]
  have hrow : position < ((rows full)[node.val]'(by rw [rows_length]; exact node.isLt)).length := by
    rw [row_get]
    simpa only [List.length_map, Array.length_toList] using hp
  rw [flatOffset, PSTRStaticLayout.flatten_getD (rows full) node.val position
    (by rw [rows_length]; exact node.isLt) hrow]
  simp only [row_get, List.getElem_map, Array.getElem_toList]

end PaperProofs.Structure.LaminarTree.PSTRCountChildRows
