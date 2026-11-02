module
public import Structure.PA17_TM_RatArithmetic_PairEncode_017b

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairEncode017

theorem pairFinal_eq (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    pairFinal footer archive a b suffix =
      ⟨47,Turing.Tape.mk₂ (false::archive) (encodeNat a ++ encodeNat b ++ footer::suffix)⟩ := by
  change (⟨(pairFinal footer archive a b suffix).q,
    (pairFinal footer archive a b suffix).Tape⟩ : MachineState 47) = _
  rw [pairFinal_label,pairFinal_tape]

theorem pair_explicit_runsFrom (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom (pairMachine footer)
      ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (PSTRTMIncrement009.blocks (payload b) ++ false::false::suffix)⟩
      (pairTrace footer archive a b suffix)
      ⟨47,Turing.Tape.mk₂ (false::archive) (encodeNat a ++ encodeNat b ++ footer::suffix)⟩ := by
  rw [← pairFinal_eq]
  exact pair_runsFrom footer archive a b suffix

theorem pair_time_le (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    (pairTrace footer archive a b suffix).length ≤ 64*((payload a).length+(payload b).length+1)^2 := by
  rw [pair_length]
  let w := (payload a).length+(payload b).length+1
  have ha : (payload a).length ≤ w := by dsimp [w]; omega
  have hb : (payload b).length ≤ w := by dsimp [w]; omega
  have hwpos : 1 ≤ w := by dsimp [w]; omega
  have ha2 := Nat.pow_le_pow_left ha 2
  have hb2 := Nat.pow_le_pow_left hb 2
  have hwsq : w ≤ w^2 := by
    simpa only [pow_two,Nat.mul_one] using Nat.mul_le_mul_left w hwpos
  have hwone : 1 ≤ w^2 := hwpos.trans hwsq
  have hf : (if footer then 1 else 0 : Nat) ≤ 1 := by cases footer <;> decide
  change (payload a).length^2+(payload b).length^2+13*(payload a).length+
    11*(payload b).length+18+(if footer then 1 else 0) ≤ 64*w^2
  omega

theorem pair_visitedSpace_le (footer : Bool) (archive : List Bool) (a b : Nat) (suffix : List Bool)
    (inputLength : Nat) :
    visitedSpace (pairMachine footer) inputLength (pairTrace footer archive a b suffix) ≤
      inputLength+128*((payload a).length+(payload b).length+1)^2+1 := by
  have hs := PSTRTMTrace002.visitedSpace_le (pairMachine footer) inputLength (pairTrace footer archive a b suffix)
  have ht := pair_time_le footer archive a b suffix
  omega

/-- Only a trailing false at the genuine far-right blank tail is removed
from the descriptor. No internal cell or left guard is removed or shifted. -/
theorem tape_trailing_false (left word : List Bool) :
    Turing.Tape.mk₂ left (word ++ [false]) = Turing.Tape.mk₂ left word := by
  simp only [Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_append_false]

def plainMachine : Machine 47 := pairMachine false
def markedMachine : Machine 47 := pairMachine true

def plainTrace (archive : List Bool) (a b : Nat) : List (MachineState 47) := pairTrace false archive a b []
def markedTrace (archive : List Bool) (a b : Nat) (suffix : List Bool) : List (MachineState 47) :=
  pairTrace true archive a b suffix

theorem plain_runsFrom (archive : List Bool) (a b : Nat) :
    PSTRTMSeq005.RunsFrom plainMachine
      ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (PSTRTMIncrement009.blocks (payload b) ++ [false,false])⟩
      (plainTrace archive a b) ⟨47,Turing.Tape.mk₂ (false::archive) (encodeNat a ++ encodeNat b)⟩ := by
  have h := pair_explicit_runsFrom false archive a b []
  rw [tape_trailing_false (false::archive) (encodeNat a ++ encodeNat b)] at h
  exact h

theorem marked_runsFrom (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom markedMachine
      ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (PSTRTMIncrement009.blocks (payload b) ++ false::false::suffix)⟩
      (markedTrace archive a b suffix)
      ⟨47,Turing.Tape.mk₂ (false::archive) (encodeNat a ++ encodeNat b ++ true::suffix)⟩ :=
  pair_explicit_runsFrom true archive a b suffix

theorem marked_framed (archive : List Bool) (a b : Nat) (suffix : List Bool) :
    ∃ trace final,
      PSTRTMSeq005.RunsFrom markedMachine
        ⟨0,Turing.Tape.mk₂ (false::aArchive archive a) (PSTRTMIncrement009.blocks (payload b) ++ false::false::suffix)⟩
        trace final ∧
      final.q = 47 ∧ final.Tape = Turing.Tape.mk₂ (false::archive) (encodeNat a ++ encodeNat b ++ true::suffix) ∧
      trace.length ≤ 64*((payload a).length+(payload b).length+1)^2 ∧
      ∀ inputLength, visitedSpace markedMachine inputLength trace ≤
        inputLength+128*((payload a).length+(payload b).length+1)^2+1 :=
  ⟨markedTrace archive a b suffix,
    ⟨47,Turing.Tape.mk₂ (false::archive) (encodeNat a ++ encodeNat b ++ true::suffix)⟩,
    marked_runsFrom archive a b suffix,rfl,rfl,pair_time_le true archive a b suffix,
    pair_visitedSpace_le true archive a b suffix⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticPairEncode017
