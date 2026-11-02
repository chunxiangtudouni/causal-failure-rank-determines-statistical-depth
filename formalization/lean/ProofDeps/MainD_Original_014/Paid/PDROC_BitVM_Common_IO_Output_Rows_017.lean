module

public import Paid.PDROC_BitVM_Common_IO_Output_Initial_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

/-- Only a mathematical slice of the existing65 cells. The encoder is
the frozen Root030 encoder, unchanged; no machine projects this vector. -/
def encodedOther (row : Wide.VMTrack) : OtherTail :=
  (FiniteTrackCodec.encode row).tail.tail.tail

theorem vector_uncons {n : Nat} (values : List.Vector Bool (n + 1)) :
    values.toList = values.head :: values.tail.toList := by
  exact (congrArg List.Vector.toList (List.Vector.cons_head_tail values)).symm

theorem encode_three_cells (row : Wide.VMTrack) :
    (FiniteTrackCodec.encode row).toList =
      row.1 :: (row.2 (0 : Fin 32)).isSome :: (row.2 (0 : Fin 32)).getD false ::
        (encodedOther row).toList := by
  let encoded : List.Vector Bool 65 := FiniteTrackCodec.encode row
  calc
    (FiniteTrackCodec.encode row).toList = encoded.head :: encoded.tail.toList := vector_uncons encoded
    _ = encoded.head :: encoded.tail.head :: encoded.tail.tail.toList :=
      congrArg (fun values => encoded.head :: values) (vector_uncons encoded.tail)
    _ = encoded.head :: encoded.tail.head :: encoded.tail.tail.head :: encoded.tail.tail.tail.toList :=
      congrArg (fun values => encoded.head :: encoded.tail.head :: values) (vector_uncons encoded.tail.tail)
    _ = _ := rfl

theorem encode_present_row (row : Wide.VMTrack) (bit : Bool)
    (value : row.2 (0 : Fin 32) = some bit) :
    (FiniteTrackCodec.encode row).toList = presentRow row.1 bit (encodedOther row) := by
  rw [encode_three_cells, value]
  rfl

theorem trackPairs_head (row : Wide.VMTrack) :
    (trackPairs row).head? = some ((row.2 (0 : Fin 32)).isSome, (row.2 (0 : Fin 32)).getD false) := rfl

def bottomDescriptors : List DataRow → List PresentRow
  | [] => []
  | current :: rest => (true, current.1, current.2) :: rest.map (fun row => (false, row.1, row.2))

theorem bottomDescriptors_length (rows : List DataRow) :
    (bottomDescriptors rows).length = rows.length := by cases rows <;> simp [bottomDescriptors]

theorem bottomDescriptors_snoc (current : DataRow) (rest : List DataRow) (last : DataRow) :
    bottomDescriptors ((current :: rest) ++ [last]) =
      bottomDescriptors (current :: rest) ++ [(false, last.1, last.2)] := by
  simp [bottomDescriptors]

theorem sourceDescriptors_reverse (rows : List DataRow) :
    sourceDescriptors rows = bottomDescriptors rows.reverse := by
  induction rows with
  | nil => rfl
  | cons current rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest =>
      rw [sourceDescriptors, ih]
      have nonempty : (next :: rest).reverse ≠ [] := by simp
      obtain ⟨first, later, shape⟩ := List.exists_cons_of_ne_nil nonempty
      have appended : bottomDescriptors ((next :: rest).reverse ++ [current]) =
          bottomDescriptors (next :: rest).reverse ++ [(false, current.1, current.2)] := by
        rw [shape, bottomDescriptors_snoc]
      simpa only [List.reverse_cons, List.isEmpty_cons] using appended.symm

theorem bottomDescriptors_get (rows : List DataRow) (index : Nat) (inside : index < rows.length) :
    (bottomDescriptors rows)[index]'(by rw [bottomDescriptors_length]; exact inside) =
      (decide (index = 0), (rows[index]).1, (rows[index]).2) := by
  cases rows with
  | nil => simp at inside
  | cons current rest =>
    cases index with
    | zero => rfl
    | succ index => simp [bottomDescriptors]

def sourceDataBottom (cells : Fin 32 → List Bool) : List DataRow :=
  List.ofFn (fun index : Fin (cells (0 : Fin 32)).length =>
    ((cells (0 : Fin 32)).reverse[index.val]'(by simp),
      encodedOther (decide (index.val = 0), rowAt cells index.val)))

theorem sourceDataBottom_length (cells : Fin 32 → List Bool) :
    (sourceDataBottom cells).length = (cells (0 : Fin 32)).length := by simp [sourceDataBottom]

theorem sourceDataBottom_bits (cells : Fin 32 → List Bool) :
    (sourceDataBottom cells).reverse.map Prod.fst = cells (0 : Fin 32) := by
  have forward : (sourceDataBottom cells).map Prod.fst = (cells (0 : Fin 32)).reverse := by
    apply List.ext_getElem <;> simp [sourceDataBottom]
  rw [List.map_reverse, forward, List.reverse_reverse]

theorem canonical_present (cells : Fin 32 → List Bool)
    (index : Fin (cells (0 : Fin 32)).length) :
    (FiniteTrackCodec.encode (decide (index.val = 0), rowAt cells index.val)).toList =
      presentRow (decide (index.val = 0))
        ((cells (0 : Fin 32)).reverse[index.val]'(by simp))
        (encodedOther (decide (index.val = 0), rowAt cells index.val)) := by
  apply encode_present_row
  exact List.getElem?_eq_getElem (by simp)

def canonicalAbsent (cells : Fin 32 → List Bool) (_positive : 0 < (cells (0 : Fin 32)).length)
    (index : Fin (stackHeight cells - (cells (0 : Fin 32)).length)) : AbsentRow := by
  let place := (cells (0 : Fin 32)).length + index.val
  have inside : place < stackHeight cells := by
    have cap := length_le_height cells (0 : Fin 32)
    have bound := index.isLt
    dsimp [place]
    omega
  let row : Wide.VMTrack := (false, rowAt cells place)
  have absent : rowAt cells place (0 : Fin 32) = none := by
    apply List.getElem?_eq_none
    simp only [List.length_reverse]
    dsimp [place]
    omega
  refine ⟨⟨trackPairs row, trackPairs_length row, ?_⟩, ?_⟩
  · obtain ⟨slot, occupied⟩ := height_inhabited_row cells ⟨place, inside⟩
    cases value : rowAt cells place slot with
    | none => simp [value] at occupied
    | some bit => exact trackPairs_some row slot bit value
  · simp only [trackPairs_head, row, absent, Option.isSome_none, Option.getD_none]

def canonicalAbove (cells : Fin 32 → List Bool) (positive : 0 < (cells (0 : Fin 32)).length) : List AbsentRow :=
  List.ofFn (canonicalAbsent cells positive)

theorem canonicalAbove_length (cells : Fin 32 → List Bool) (positive : 0 < (cells (0 : Fin 32)).length) :
    (canonicalAbove cells positive).length = stackHeight cells - (cells (0 : Fin 32)).length := by
  simp [canonicalAbove]

theorem canonicalAbsent_bits (cells : Fin 32 → List Bool) (positive : 0 < (cells (0 : Fin 32)).length)
    (index : Fin (stackHeight cells - (cells (0 : Fin 32)).length)) :
    occupiedBits (canonicalAbsent cells positive index).row =
      (FiniteTrackCodec.encode (false, rowAt cells ((cells (0 : Fin 32)).length + index.val))).toList := by
  change false :: pairBits (trackPairs (false, rowAt cells ((cells (0 : Fin 32)).length + index.val))) = _
  exact (encode_row_pairs (false, rowAt cells ((cells (0 : Fin 32)).length + index.val))).symm

theorem canonical_split (cells : Fin 32 → List Bool) (positive : 0 < (cells (0 : Fin 32)).length) :
    canonicalTracks cells =
      List.ofFn (fun index : Fin (cells (0 : Fin 32)).length =>
        (decide (index.val = 0), rowAt cells index.val)) ++
      List.ofFn (fun index : Fin (stackHeight cells - (cells (0 : Fin 32)).length) =>
        (false, rowAt cells ((cells (0 : Fin 32)).length + index.val))) := by
  have width := length_le_height cells (0 : Fin 32)
  have lifted : canonicalTracks cells =
      List.ofFn (fun index : Fin ((cells (0 : Fin 32)).length +
        (stackHeight cells - (cells (0 : Fin 32)).length)) =>
        (decide (index.val = 0), rowAt cells index.val)) := by
    apply List.ext_getElem
    · simp [canonicalTracks, Nat.add_sub_of_le width]
    · intro index _ _
      simp [canonicalTracks]
  rw [lifted, List.ofFn_add]
  congr 1
  apply congrArg List.ofFn
  funext index
  have nonzero : (cells (0 : Fin 32)).length + index.val ≠ 0 := by omega
  simp only [Fin.natAdd, nonzero, decide_false]

/-- Derive the ENTIRE physical initial extraction frame from all32
actual source stacks. The first stack supplies only the output word;
every other stack is preserved in the derived old-data tails. The
maximum height is derived here, never passed to the finite controller. -/
theorem canonical_frame (cells : Fin 32 → List Bool) (positive : 0 < (cells (0 : Fin 32)).length) :
    (canonicalTracks cells).flatMap (fun row => (FiniteTrackCodec.encode row).toList) =
      (unreadLeft (sourceDataBottom cells).reverse).reverse ++
        flatRows (absentTails (canonicalAbove cells positive)) := by
  have sourceRows :
      (List.ofFn (fun index : Fin (cells (0 : Fin 32)).length =>
        (decide (index.val = 0), rowAt cells index.val))).map
          (fun row => (FiniteTrackCodec.encode row).toList) =
      (bottomDescriptors (sourceDataBottom cells)).map
        (fun row => presentRow row.1 row.2.1 row.2.2) := by
    apply List.ext_getElem
    · simp [bottomDescriptors_length, sourceDataBottom_length]
    · intro index inside _
      have cap : index < (cells (0 : Fin 32)).length := by simpa using inside
      have descriptor := bottomDescriptors_get (sourceDataBottom cells) index
        (by rw [sourceDataBottom_length]; exact cap)
      simp only [List.getElem_map, List.getElem_ofFn]
      simp only [descriptor]
      simpa only [sourceDataBottom, List.getElem_ofFn] using canonical_present cells ⟨index, cap⟩
  have sourceFlat :
      (List.ofFn (fun index : Fin (cells (0 : Fin 32)).length =>
        (decide (index.val = 0), rowAt cells index.val))).flatMap
          (fun row => (FiniteTrackCodec.encode row).toList) =
      (unreadLeft (sourceDataBottom cells).reverse).reverse := by
    have flattened := congrArg List.flatten sourceRows
    rw [← List.flatMap_def, ← List.flatMap_def] at flattened
    have descriptors : sourceDescriptors (sourceDataBottom cells).reverse =
        bottomDescriptors (sourceDataBottom cells) := by
      simpa only [List.reverse_reverse] using sourceDescriptors_reverse (sourceDataBottom cells).reverse
    rw [← descriptors] at flattened
    exact flattened.trans (sourceDescriptors_bits _)
  have aboveFlat :
      (List.ofFn (fun index : Fin (stackHeight cells - (cells (0 : Fin 32)).length) =>
        (false, rowAt cells ((cells (0 : Fin 32)).length + index.val)))).flatMap
          (fun row => (FiniteTrackCodec.encode row).toList) =
      occupiedRows ((canonicalAbove cells positive).map AbsentRow.row) := by
    unfold occupiedRows
    rw [List.flatMap_map]
    apply congrArg List.flatten
    rw [List.map_ofFn]
    unfold canonicalAbove
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext index
    exact (canonicalAbsent_bits cells positive index).symm
  rw [canonical_split cells positive, List.flatMap_append, sourceFlat, aboveFlat, absent_flat]

end PDROC.BitVM.Common.IO.Output
