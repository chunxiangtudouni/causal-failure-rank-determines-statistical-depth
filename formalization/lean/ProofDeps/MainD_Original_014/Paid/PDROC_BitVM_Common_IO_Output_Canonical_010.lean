module

public import Paid.PDROC_BitVM_Common_IO_Wide_Codec_003
public import Paid.PDROC_BitVM_Common_TM2_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Common.IO.Output

open Turing
open PaperProofs.Common.Native.PSTRWordBool

attribute [local implicit_reducible] Turing.TM2to1.Γ'

abbrev StackRows := Fin 32 → Option Bool

/-- All functions in this module are mathematical representations of
ALREADY EXISTING cells. None is a machine instruction, store or input. -/
def stackHeight (cells : Fin 32 → List Bool) : Nat := Finset.univ.sup (fun slot => (cells slot).length)

def rowAt (cells : Fin 32 → List Bool) (index : Nat) : StackRows :=
  fun slot => (cells slot).reverse[index]?

def canonicalRows (cells : Fin 32 → List Bool) : List StackRows :=
  List.ofFn (fun index : Fin (stackHeight cells) => rowAt cells index.val)

theorem length_le_height (cells : Fin 32 → List Bool) (slot : Fin 32) :
    (cells slot).length ≤ stackHeight cells :=
  Finset.le_sup (f := fun point => (cells point).length) (Finset.mem_univ slot)

theorem rowAt_after_height (cells : Fin 32 → List Bool) (index : Nat)
    (outside : stackHeight cells ≤ index) (slot : Fin 32) : rowAt cells index slot = none := by
  apply List.getElem?_eq_none
  simpa only [List.length_reverse] using (length_le_height cells slot).trans outside

theorem canonicalRows_nth (cells : Fin 32 → List Bool) (index : Nat) :
    (ListBlank.mk (canonicalRows cells)).nth index = rowAt cells index := by
  by_cases inside : index < stackHeight cells
  · simp [canonicalRows, List.getI_eq_getElem?_getD, inside]
  · simp only [ListBlank.nth_mk, canonicalRows, List.getI_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_right inside, Option.getD_none]
    funext slot
    exact (rowAt_after_height cells index (by omega) slot).symm

/-- Direct reuse of Mathlib's genuine stack projection invariant.
The canonical list is derived from the ACTUAL changed tracks, with no
caller-supplied numeric/blank-boundary eligibility or new run assumption. -/
theorem actual_tracks_canonical (cells : Fin 32 → List Bool) (changed : ListBlank StackRows)
    (represented : ∀ slot, changed.map (proj slot) = ListBlank.mk ((cells slot).map some).reverse) :
    changed = ListBlank.mk (canonicalRows cells) := by
  apply ListBlank.ext
  intro index
  rw [canonicalRows_nth]
  funext slot
  exact TM2to1.stk_nth_val index (represented slot)

theorem height_inhabited_row (cells : Fin 32 → List Bool) (index : Fin (stackHeight cells)) :
    ∃ slot : Fin 32, (rowAt cells index.val slot).isSome = true := by
  have someLength : ∃ slot : Fin 32, index.val < (cells slot).length := by
    by_contra missing
    have every : ∀ slot : Fin 32, (cells slot).length ≤ index.val := by
      intro slot
      by_contra large
      exact missing ⟨slot, by omega⟩
    have cap : stackHeight cells ≤ index.val := Finset.sup_le (fun slot _ => every slot)
    exact (Nat.not_le_of_lt index.isLt) cap
  obtain ⟨slot, inside⟩ := someLength
  refine ⟨slot, ?_⟩
  cases value : (cells slot).reverse[index.val]? with
  | none =>
    have outside := List.getElem?_eq_none_iff.mp value
    simp only [List.length_reverse] at outside
    omega
  | some bit => simp only [rowAt, value, Option.isSome_some]

def canonicalTracks (cells : Fin 32 → List Bool) : List Wide.VMTrack :=
  List.ofFn (fun index : Fin (stackHeight cells) => (decide (index.val = 0), rowAt cells index.val))

theorem canonicalTracks_nth (cells : Fin 32 → List Bool) (positive : 0 < stackHeight cells) (index : Nat) :
    (ListBlank.mk (canonicalTracks cells)).nth index = (decide (index = 0), rowAt cells index) := by
  by_cases inside : index < stackHeight cells
  · simp [canonicalTracks, List.getI_eq_getElem?_getD, inside]
  · have nonzero : index ≠ 0 := by omega
    simp only [ListBlank.nth_mk, canonicalTracks, List.getI_eq_getElem?_getD, List.getElem?_ofFn,
      dite_eq_right inside, Option.getD_none, nonzero, decide_false]
    apply Prod.ext
    · rfl
    · funext slot
      exact (rowAt_after_height cells index (by omega) slot).symm

theorem addBottom_nth (changed : ListBlank StackRows) (index : Nat) :
    (TM2to1.addBottom changed).nth index = (decide (index = 0), changed.nth index) := by
  apply Prod.ext
  · cases index with
    | zero => simpa using TM2to1.addBottom_head_fst changed
    | succ index => simpa using TM2to1.addBottom_nth_succ_fst changed index
  · exact TM2to1.addBottom_nth_snd changed index

theorem actual_addBottom_canonical (cells : Fin 32 → List Bool) (positive : 0 < stackHeight cells)
    (changed : ListBlank StackRows)
    (represented : ∀ slot, changed.map (proj slot) = ListBlank.mk ((cells slot).map some).reverse) :
    TM2to1.addBottom changed = ListBlank.mk (canonicalTracks cells) := by
  apply ListBlank.ext
  intro index
  rw [addBottom_nth, canonicalTracks_nth cells positive, actual_tracks_canonical cells changed represented,
    canonicalRows_nth]

/-- Thin definitional tape compatibility, reusing Mathlib's existing
pointed tape-map theorem. No new codec or transition system is defined. -/
theorem encoded_tape_rows (rows : List Wide.VMTrack) :
    TM1to1.trTape (FiniteTrackCodec.encode_default 32) (Tape.mk₁ rows) =
      Tape.mk₁ (rows.flatMap (fun row => (FiniteTrackCodec.encode row).toList)) := by
  rw [Tape.mk₁, Tape.mk₂, TM1to1.trTape_mk']
  unfold TM1to1.trTape'
  simp only [ListBlank.flatMap_mk, List.flatMap_nil]
  rfl

/-- WHOLE actual Root025/040 final tape, head still at bottom, becomes
exactly the finite65-row physical frame derived from its source cells.
All other cells remain part of the frame and of its actual footprint. -/
theorem actual_encoded_tape_canonical (cells : Fin 32 → List Bool) (positive : 0 < stackHeight cells)
    (changed : ListBlank StackRows)
    (represented : ∀ slot, changed.map (proj slot) = ListBlank.mk ((cells slot).map some).reverse) :
    TM1to1.trTape (FiniteTrackCodec.encode_default 32) (ScannerPaths.baseTape changed) =
      Tape.mk₁ ((canonicalTracks cells).flatMap (fun row => (FiniteTrackCodec.encode row).toList)) := by
  unfold ScannerPaths.baseTape
  rw [actual_addBottom_canonical cells positive changed represented]
  exact encoded_tape_rows (canonicalTracks cells)

end PDROC.BitVM.Common.IO.Output
