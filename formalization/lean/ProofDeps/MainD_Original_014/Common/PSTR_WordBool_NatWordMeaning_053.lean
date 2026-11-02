module

public import Common.PSTR_WordBool_NatWordRead_051
public import Common.PSTR_WordBool_NatWordFinish_052

/-! Canonical result semantics derived from the SAME callee's whole Tape.
Explicit finite FALSE padding is immaterial to ListBlank reads. The actual
copy-plus-pad output denotes exactly the original Word truncation, including
zero-width and zero-valued words. This file supplies no executable answers. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.NatWordIO

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

theorem header_length_le (length : Nat) (payload : ListBlank Bool) (right : List Bool)
    (certificate : Header length payload right) : length ≤ right.length := by
  induction length generalizing right with
  | zero => omega
  | succ length ih =>
    have observed := header_succ_observed length payload right certificate
    cases right with
    | nil => cases observed
    | cons bit right =>
      have remaining := ih right (header_tail length payload (bit :: right) certificate)
      simp only [List.length_cons]
      omega

theorem header_payload (length : Nat) (payload : ListBlank Bool) (right : List Bool)
    (certificate : Header length payload right) :
    ListBlank.mk (right.drop (length + 1)) = payload := by
  induction length generalizing right with
  | zero =>
    change ListBlank.mk right = ListBlank.cons false payload at certificate
    change ListBlank.mk (right.drop 1) = payload
    rw [List.drop_one, ← ListBlank.tail_mk, certificate, ListBlank.tail_cons]
  | succ length ih =>
    have remaining := ih right.tail (header_tail length payload right certificate)
    rw [List.drop_tail] at remaining
    exact remaining

theorem quoted_getD (left right : List Bool) (same : ListBlank.mk left = ListBlank.mk right)
    (point : Nat) : left.getD point false = right.getD point false := by
  have sameBit := congrArg (fun tape : ListBlank Bool => tape.nth point) same
  calc
    _ = left.getI point := List.getD_default_eq_getI (l := left) (n := point)
    _ = right.getI point := sameBit
    _ = right.getD point false := (List.getD_default_eq_getI (l := right) (n := point)).symm

theorem quoted_payload_getD (value : Nat) (right : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (PSTRTMNatValue017.rawPayload value))
    (point : Nat) : right.getD point false = value.testBit point :=
  (quoted_getD right (PSTRTMNatValue017.rawPayload value) same point).trans (rawPayload_getD value point)

theorem readBits_getElem (count : Nat) (right : List Bool) (point : Nat) (within : point < count) :
    (readBits count right)[point]'(by rw [readBits_length]; exact within) = right.getD point false := by
  simp only [readBits, List.getElem_ofFn]

theorem payload_high_false (value : Nat) (right : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (PSTRTMNatValue017.rawPayload value))
    (point : Nat) (beyond : natBits value ≤ point) : right.getD point false = false := by
  rw [quoted_payload_getD value right same point]
  apply Nat.testBit_eq_false_of_lt
  exact lt_of_lt_of_le (PSTRTMCodec001.natBits_bound value)
    (Nat.pow_le_pow_right (by decide) beyond)

theorem padded_readBits (value width : Nat) (right : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (PSTRTMNatValue017.rawPayload value)) :
    readBits (min (natBits value) width) right ++
        List.replicate (width - min (natBits value) width) false = readBits width right := by
  have limited : min (natBits value) width ≤ width := Nat.min_le_right _ _
  apply List.ext_getElem
  · simp only [List.length_append, readBits_length, List.length_replicate]
    omega
  · intro point inLeft inRight
    have within : point < width := by simpa only [readBits_length] using inRight
    by_cases early : point < min (natBits value) width
    · have earlyList : point < (readBits (min (natBits value) width) right).length := by
        rw [readBits_length]
        exact early
      calc
        _ = (readBits (min (natBits value) width) right)[point] := List.getElem_append_left earlyList
        _ = right.getD point false := readBits_getElem _ right point early
        _ = (readBits width right)[point] := (readBits_getElem width right point within).symm
    · have laterList : (readBits (min (natBits value) width) right).length ≤ point := by
        rw [readBits_length]
        exact Nat.le_of_not_gt early
      have beyond : natBits value ≤ point := by
        by_cases order : natBits value ≤ width
        · rw [Nat.min_eq_left order] at early
          exact Nat.le_of_not_gt early
        · have order' : width ≤ natBits value := Nat.le_of_lt (Nat.lt_of_not_ge order)
          rw [Nat.min_eq_right order'] at early
          exact False.elim (early within)
      calc
        _ = false := by rw [List.getElem_append_right laterList, List.getElem_replicate]
        _ = right.getD point false := (payload_high_false value right same point beyond).symm
        _ = (readBits width right)[point] := (readBits_getElem width right point within).symm

theorem reversed_padded_bits (kept padding : Nat) (right : List Bool) :
    (List.replicate padding false ++ (readBits kept right).reverse).reverse =
      readBits kept right ++ List.replicate padding false := by
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate]

theorem word_of_readBits (value width : Nat) (right : List Bool)
    (same : ListBlank.mk right = ListBlank.mk (PSTRTMNatValue017.rawPayload value)) :
    BitVec.ofNat width (PSTRTMIncrement009.valueDigits (readBits width right)) =
      BitVec.ofNat width value := by
  apply BitVec.eq_of_getLsbD_eq
  intro point within
  have read : (readBits width right).getI point = right.getD point false := by
    rw [List.getI_eq_getElem _ (by rw [readBits_length]; exact within)]
    exact readBits_getElem width right point within
  have sameBit : (PSTRTMIncrement009.valueDigits (readBits width right)).testBit point = value.testBit point := by
    rw [PSTRTMNatValue017.testBit_valueDigits, read]
    exact quoted_payload_getD value right same point
  simp only [BitVec.getLsbD_ofNat, sameBit]

end PaperProofs.Common.Native.PSTRWordBool.NatWordIO
