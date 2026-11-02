module
public import Structure.PA17_TM_RatArithmetic_Sign_003b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSign003

theorem numerator_zero_iff (x : ℚ) : x.num.natAbs = 0 ↔ x = 0 := by
  rw [Int.natAbs_eq_zero,Rat.num_eq_zero]

theorem sign_neg (x : ℚ) : decide (-x < 0) = changedSign x.num.natAbs (decide (x < 0)) := by
  by_cases hz : x = 0
  · subst x
    simp [changedSign]
  · have hn : x.num.natAbs ≠ 0 := (numerator_zero_iff x).not.mpr hz
    by_cases hl : x < 0
    · have hneg : ¬ -x < 0 := by linarith
      simp [changedSign,hn,hl,hneg]
    · have hp : 0 < x := by rcases lt_trichotomy x 0 with h | h | h <;> tauto
      have hneg : -x < 0 := by linarith
      simp [changedSign,hn,hl,hneg]

theorem neg_payload (x : ℚ) :
    encodeNat (-x).num.natAbs ++ encodeNat (-x).den = encodeNat x.num.natAbs ++ encodeNat x.den := by
  rw [Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den]

def datumTrace (x : ℚ) (left suffix : List Bool) : List (MachineState 15) :=
  natTrace x.num.natAbs (decide (x < 0)) left (encodeNat x.den ++ suffix)

def datumInitial (x : ℚ) (left suffix : List Bool) : MachineState 15 :=
  state 0 left (encodeDatum (.rational x) ++ suffix)

def datumFinal (x : ℚ) (left suffix : List Bool) : MachineState 15 :=
  state 15 left (encodeDatum (.rational (-x)) ++ suffix)

theorem negateDatum_runsFrom (x : ℚ) (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom negateDatumMachine (datumInitial x left suffix)
      (datumTrace x left suffix) (datumFinal x left suffix) := by
  have run := nat_runsFrom x.num.natAbs (decide (x < 0)) left (encodeNat x.den ++ suffix)
  simpa only [datumInitial,datumFinal,datumTrace,encodeDatum,List.cons_append,List.nil_append,
    List.append_assoc,← sign_neg x,Rat.num_neg_eq_neg_num,Int.natAbs_neg,Rat.den_neg_eq_den] using run

theorem negateDatum_final_tape (x : ℚ) (left suffix : List Bool) :
    (datumFinal x left suffix).Tape = Turing.Tape.mk₂ left (encodeDatum (.rational (-x)) ++ suffix) := rfl

theorem negateDatum_final_label (x : ℚ) (left suffix : List Bool) : (datumFinal x left suffix).q = 15 := rfl

theorem negateDatumTrace_length_le (x : ℚ) (left suffix : List Bool) :
    (datumTrace x left suffix).length ≤ 10 := natTrace_length_le _ _ _ _

theorem negateDatum_visitedSpace_le (x : ℚ) (left suffix : List Bool) (inputLength : Nat) :
    visitedSpace negateDatumMachine inputLength (datumTrace x left suffix) ≤ inputLength+32 := by
  have hs := PSTRTMTrace002.visitedSpace_le negateDatumMachine inputLength (datumTrace x left suffix)
  have ht := negateDatumTrace_length_le x left suffix
  omega

theorem negateDatum_framed (x : ℚ) (left suffix : List Bool) :
    ∃ trace final,
      PSTRTMSeq005.RunsFrom negateDatumMachine
        ⟨0,Turing.Tape.mk₂ left (encodeDatum (.rational x) ++ suffix)⟩ trace final ∧
      final.q = 15 ∧ final.Tape = Turing.Tape.mk₂ left (encodeDatum (.rational (-x)) ++ suffix) ∧
      trace.length ≤ 10 ∧
      ∀ inputLength, visitedSpace negateDatumMachine inputLength trace ≤ inputLength+32 :=
  ⟨datumTrace x left suffix,datumFinal x left suffix,negateDatum_runsFrom x left suffix,
    rfl,rfl,negateDatumTrace_length_le x left suffix,negateDatum_visitedSpace_le x left suffix⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSign003
