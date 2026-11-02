module

public import Structure.PA17_TM_Division_Loop_002h

/-! Numerical interpretation of the SAME resident/quotient fold. The
initial zero branch is identified from the actual compare control, and
all subsequent divisor digits are preserved cell for cell. -/

@[expose] public section
set_option maxRecDepth 22000
set_option maxHeartbeats 2200000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
open PSTRTMBinaryAdd024 PSTRTMIncrement009 PSTRTMCompareCode054

def initialZeroMode (resident : List (Bool × Bool)) : Bool :=
  decide ((resultRelation 0 resident).val = 0)

theorem initialZeroMode_correct (resident : List (Bool × Bool)) (hr : firstValue resident = 0) :
    initialZeroMode resident = decide (secondValue resident = 0) := by
  unfold initialZeroMode
  rw [PSTRTMCompareValue056.resultRelation_classify,hr]
  by_cases hb : secondValue resident = 0
  · simp [PSTRTMCompareValue056.classify,hb]
  · have hp : 0 < secondValue resident := by omega
    have hn : (0 : Nat) ≠ secondValue resident := by omega
    simp [PSTRTMCompareValue056.classify,hb,hp,hn]

theorem shift_second_digits (bit : Bool) (resident : List (Bool × Bool)) :
    (PSTRTMShiftColumnCode065.shiftPairs bit resident).map Prod.snd = resident.map Prod.snd := by
  induction resident generalizing bit with
  | nil => rfl
  | cons pair later ih =>
    rcases pair with ⟨a,b⟩
    simp only [PSTRTMShiftColumnCode065.shiftPairs,List.map_cons,ih]

theorem residentNext_second_digits (zeroMode bit : Bool) (resident : List (Bool × Bool)) :
    (residentNext zeroMode bit resident).map Prod.snd = resident.map Prod.snd := by
  unfold residentNext
  split <;> simp only [PA17TMDivisionSub001.subPairs_second,shift_second_digits]

theorem loopValues_second_digits (zeroMode : Bool) (remaining quotient : List Bool) (resident : List (Bool × Bool)) :
    (loopValues zeroMode remaining quotient resident).2.map Prod.snd = resident.map Prod.snd := by
  induction remaining generalizing quotient resident with
  | nil => rfl
  | cons bit later ih =>
    change (loopValues zeroMode later (residentEmit zeroMode bit resident :: quotient)
      (residentNext zeroMode bit resident)).2.map Prod.snd = _
    rw [ih,residentNext_second_digits]

theorem loopValues_original_data (source : List Bool) (resident : List (Bool × Bool))
    (hr : firstValue resident = 0) (width : source.length ≤ resident.length) :
    let final := loopValues (initialZeroMode resident) source.reverse [] resident
    valueDigits final.1 = valueDigits source / secondValue resident ∧
      firstValue final.2 = valueDigits source % secondValue resident ∧
      final.1.length = source.length ∧ final.2.length = resident.length ∧
      final.2.map Prod.snd = resident.map Prod.snd := by
  have hc := loopValues_correct (secondValue resident) (initialZeroMode resident) source.reverse [] resident
    (initialZeroMode_correct resident hr) rfl hr (by simpa only [List.length_reverse,List.length_nil,Nat.add_zero] using width)
  simp only [quotientDigits,List.reverse_reverse,List.append_nil] at hc
  have hv : valueDigits (loopValues (initialZeroMode resident) source.reverse [] resident).1 =
      valueDigits source / secondValue resident := by
    rw [hc.1,quotientDigits_value,quotRem_correct]
  have hm : firstValue (loopValues (initialZeroMode resident) source.reverse [] resident).2 =
      valueDigits source % secondValue resident := by
    rw [hc.2,quotRem_correct]
  have hl := loopValues_length (initialZeroMode resident) source.reverse [] resident
  simp only [List.length_reverse,List.length_nil,Nat.add_zero] at hl
  exact ⟨hv,hm,hl.1,hl.2.1,loopValues_second_digits _ _ _ _⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionLoop002
