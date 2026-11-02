module
public import Common.PSTR_TM_ColumnRewind_067

/-! Blank-tail normalization only: no write, erase or head reset is hidden
here. A nonblank archive cannot be removed by any of these identities. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionTape005

open PSTRTMCompareCode054 PSTRTMBinaryAdd024

theorem blank_false_suffix (bits : List Bool) (count : Nat) :
    Turing.ListBlank.mk (bits ++ List.replicate count false) = Turing.ListBlank.mk bits := by
  induction count with
  | zero => simp only [List.replicate_zero, List.append_nil]
  | succ count ih =>
    rw [List.replicate_succ', ← List.append_assoc, PSTRTMRawNat010.blank_append_false, ih]

theorem blank_owned00 (bits : List Bool) :
    Turing.ListBlank.mk (bits ++ [false, false]) = Turing.ListBlank.mk bits :=
  blank_false_suffix bits 2

theorem tape_owned00 (left right : List Bool) :
    Turing.Tape.mk₂ left (right ++ [false, false]) = Turing.Tape.mk₂ left right := by
  simp only [Turing.Tape.mk₂, blank_owned00]

theorem tape_blank_left (right : List Bool) (count : Nat) :
    Turing.Tape.mk₂ (List.replicate count false) right = Turing.Tape.mk₁ right := by
  have hb : Turing.ListBlank.mk (List.replicate count false) = Turing.ListBlank.mk ([] : List Bool) := by
    simpa only [List.nil_append] using blank_false_suffix [] count
  simp only [Turing.Tape.mk₂, Turing.Tape.mk₁, hb]

theorem initial_owned00 (columns : List Bool) :
    Turing.Tape.mk₂ [false, false, false] (columns ++ [false, false]) = Turing.Tape.mk₁ columns := by
  rw [tape_owned00]
  exact tape_blank_left columns 3

theorem leftColumns_reverse (pairs : List (Bool × Bool)) :
    leftColumns pairs.reverse = (operandColumns pairs).reverse := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    simp only [List.reverse_cons, leftColumns, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, operandColumns, List.cons_append, List.nil_append] at ih ⊢
    simpa [List.append_assoc] using
      congrArg (fun tail => tail ++ [true,b,true,a]) ih

theorem resident_layout (archive : List (Bool × Bool)) (resident : List Bool) :
    Turing.Tape.mk₂ (false :: false :: false :: leftColumns archive.reverse)
      (resident ++ [false,false]) =
    Turing.Tape.mk₂ (false :: false :: false :: (operandColumns archive).reverse) resident := by
  rw [leftColumns_reverse, tape_owned00]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionTape005
