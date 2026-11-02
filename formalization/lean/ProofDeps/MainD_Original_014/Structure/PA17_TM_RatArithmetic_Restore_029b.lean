module
public import Structure.PA17_TM_RatArithmetic_Restore_029a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRestore029
open PA17TMDivisionCompose006

def budget (tail : List Bool) (gap : Nat) : Nat :=
  ((false::tail).length+1)*((false::tail).length+gap+1)

theorem trace_length (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    (trace p which memory archive tail gap).length =
      (PA17TMRatArithmeticBankCopy024.copyTrace archive (false::tail) gap).length+2 := by
  simp only [trace,List.length_map,rowTrace_length]

theorem trace_exact_length (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    (trace p which memory archive tail gap).length =
      4*(tail.length+1)^2+26*(tail.length+1)+2*gap*(tail.length+1)+3*gap+22 := by
  simp only [trace_length,PA17TMRatArithmeticBankCopy024.copy_length,List.length_cons]

theorem time_le (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    (trace p which memory archive tail gap).length ≤ 64*budget tail gap+2 := by
  rw [trace_length]
  exact Nat.add_le_add_right (PA17TMRatArithmeticBankCopy024.copy_time_le archive (false::tail) gap) 2

theorem prefix_time_le (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool)
    (gap prefixLength : Nat) :
    ((trace p which memory archive tail gap).take prefixLength).length ≤ 64*budget tail gap+2 := by
  have ht := time_le p which memory archive tail gap
  have hp : ((trace p which memory archive tail gap).take prefixLength).length ≤
      (trace p which memory archive tail gap).length := by
    simp only [List.length_take]
    omega
  exact hp.trans ht

theorem prefix_space_le (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool)
    (gap prefixLength inputLength : Nat) :
    visitedSpace (machine p which) inputLength ((trace p which memory archive tail gap).take prefixLength) ≤
      inputLength+128*budget tail gap+5 := by
  have hs := PSTRTMTrace002.visitedSpace_le (machine p which) inputLength
    ((trace p which memory archive tail gap).take prefixLength)
  have ht := prefix_time_le p which memory archive tail gap prefixLength
  omega

theorem space_le (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool)
    (gap inputLength : Nat) :
    visitedSpace (machine p which) inputLength (trace p which memory archive tail gap) ≤
      inputLength+128*budget tail gap+5 := by
  have hs := PSTRTMTrace002.visitedSpace_le (machine p which) inputLength (trace p which memory archive tail gap)
  have ht := time_le p which memory archive tail gap
  omega

theorem final_eq (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    final p which memory archive tail gap =
      ⟨label memory (60 : Fin 61),Turing.Tape.mk₂ (outputLeft archive tail gap)
        (PSTRTMIncrement009.blocks (memory.val.testBit which::tail) ++ [false,false])⟩ := rfl

theorem explicit_runsFrom (p which : Nat) (memory : Fin (p+1)) (archive tail : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom (machine p which) (initial p memory archive tail gap)
      (trace p which memory archive tail gap)
      ⟨label memory (60 : Fin 61),Turing.Tape.mk₂ (outputLeft archive tail gap)
        (PSTRTMIncrement009.blocks (memory.val.testBit which::tail) ++ [false,false])⟩ := by
  rw [← final_eq]
  exact runsFrom p which memory archive tail gap

/-- Incoming memory is a real finite-control entry, not an extra tape flag.
The hbit premise describes what its actual earlier read saved. -/
theorem restored32_runsFrom (which : Nat) (memory : Fin 32) (archive digits : List Bool) (gap : Nat)
    (hne : digits≠[]) (hbit : memory.val.testBit which=PA17TMRatArithmeticBookmark014.observedFirst digits) :
    PSTRTMSeq005.RunsFrom (machine32 which) (initial 31 memory archive digits.tail gap)
      (trace 31 which memory archive digits.tail gap)
      ⟨label memory (60 : Fin 61),Turing.Tape.mk₂ (outputLeft archive digits.tail gap)
        (PSTRTMIncrement009.blocks digits ++ [false,false])⟩ := by
  have hd := PA17TMRatArithmeticBookmark014.restoredDigits_eq memory which digits hne hbit
  change memory.val.testBit which::digits.tail=digits at hd
  have h := explicit_runsFrom 31 which memory archive digits.tail gap
  rw [hd] at h
  exact h

/-- The sixth bit is preserved as part of the actual 64-row control port.
No statement here manufactures that bit or resets the incoming register. -/
theorem restored64_runsFrom (which : Nat) (memory : Fin 64) (archive digits : List Bool) (gap : Nat)
    (hne : digits≠[]) (hbit : memory.val.testBit which=PA17TMRatArithmeticBookmark014.observedFirst digits) :
    PSTRTMSeq005.RunsFrom (machine64 which) (initial 63 memory archive digits.tail gap)
      (trace 63 which memory archive digits.tail gap)
      ⟨label memory (60 : Fin 61),Turing.Tape.mk₂ (outputLeft archive digits.tail gap)
        (PSTRTMIncrement009.blocks digits ++ [false,false])⟩ := by
  have hd : memory.val.testBit which::digits.tail=digits := by
    rw [hbit]
    exact (PA17TMRatArithmeticBookmark014.digits_observedFirst digits hne).symm
  have h := explicit_runsFrom 63 which memory archive digits.tail gap
  rw [hd] at h
  exact h

def dyMachine32 : Machine 1951 := machine32 0
def nyMachine32 : Machine 1951 := machine32 1
def dxMachine32 : Machine 1951 := machine32 3
def nxMachine32 : Machine 1951 := machine32 4

theorem dy32_runsFrom (x y : Rat) (archive : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom dyMachine32
      (initial 31 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.denominatorDigits y).tail gap)
      (trace 31 0 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.denominatorDigits y).tail gap)
      ⟨label (PA17TMRatArithmeticBookmark014.mNx x y) (60 : Fin 61),
        Turing.Tape.mk₂ (outputLeft archive (PA17TMRatArithmeticParse002.denominatorDigits y).tail gap)
          (PSTRTMIncrement009.blocks (PA17TMRatArithmeticParse002.denominatorDigits y) ++ [false,false])⟩ :=
  restored32_runsFrom 0 _ _ _ _ (PA17TMRatArithmeticBookmark014.denominator_ne_nil y)
    (PA17TMRatArithmeticBookmark014.observed_memory_bits x y).1

theorem ny32_runsFrom (x y : Rat) (archive : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom nyMachine32
      (initial 31 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.numeratorDigits y).tail gap)
      (trace 31 1 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.numeratorDigits y).tail gap)
      ⟨label (PA17TMRatArithmeticBookmark014.mNx x y) (60 : Fin 61),
        Turing.Tape.mk₂ (outputLeft archive (PA17TMRatArithmeticParse002.numeratorDigits y).tail gap)
          (PSTRTMIncrement009.blocks (PA17TMRatArithmeticParse002.numeratorDigits y) ++ [false,false])⟩ :=
  restored32_runsFrom 1 _ _ _ _ (PA17TMRatArithmeticBookmark014.numerator_ne_nil y)
    (PA17TMRatArithmeticBookmark014.observed_memory_bits x y).2.1

theorem dx32_runsFrom (x y : Rat) (archive : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom dxMachine32
      (initial 31 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.denominatorDigits x).tail gap)
      (trace 31 3 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.denominatorDigits x).tail gap)
      ⟨label (PA17TMRatArithmeticBookmark014.mNx x y) (60 : Fin 61),
        Turing.Tape.mk₂ (outputLeft archive (PA17TMRatArithmeticParse002.denominatorDigits x).tail gap)
          (PSTRTMIncrement009.blocks (PA17TMRatArithmeticParse002.denominatorDigits x) ++ [false,false])⟩ :=
  restored32_runsFrom 3 _ _ _ _ (PA17TMRatArithmeticBookmark014.denominator_ne_nil x)
    (PA17TMRatArithmeticBookmark014.observed_memory_bits x y).2.2.2.1

theorem nx32_runsFrom (x y : Rat) (archive : List Bool) (gap : Nat) :
    PSTRTMSeq005.RunsFrom nxMachine32
      (initial 31 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.numeratorDigits x).tail gap)
      (trace 31 4 (PA17TMRatArithmeticBookmark014.mNx x y) archive (PA17TMRatArithmeticParse002.numeratorDigits x).tail gap)
      ⟨label (PA17TMRatArithmeticBookmark014.mNx x y) (60 : Fin 61),
        Turing.Tape.mk₂ (outputLeft archive (PA17TMRatArithmeticParse002.numeratorDigits x).tail gap)
          (PSTRTMIncrement009.blocks (PA17TMRatArithmeticParse002.numeratorDigits x) ++ [false,false])⟩ :=
  restored32_runsFrom 4 _ _ _ _ (PA17TMRatArithmeticBookmark014.numerator_ne_nil x)
    (PA17TMRatArithmeticBookmark014.observed_memory_bits x y).2.2.2.2

theorem bookmark_actual_memory (x y : Rat) :
    Runs PA17TMRatArithmeticBookmark014.rawBookmarkMachine (encode [.rational x,.rational y])
      (PA17TMRatArithmeticBookmark014.rawBookmarkTrace x y) (PA17TMRatArithmeticBookmark014.rawBookmarkFinal x y) ∧
    (PA17TMRatArithmeticBookmark014.rawBookmarkFinal x y).q.val =
      2210+6*(PA17TMRatArithmeticBookmark014.mNx x y).val := by
  refine ⟨PA17TMRatArithmeticBookmark014.rawBookmark_runs x y,?_⟩
  have h := PA17TMRatArithmeticBookmark014.rawBookmark_final_label x y
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticRestore029
