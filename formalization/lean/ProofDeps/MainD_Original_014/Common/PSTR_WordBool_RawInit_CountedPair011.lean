module

public import Common.PSTR_WordBool_RawInit_GenericPair010
public import Common.PSTR_WordBool_CountTwo_Core001

/-! The original RCC header, its physically saved copy, two real
decrements and two arbitrary-tag Datum parsers form ONE finite program.
The counter qualification is proved from the original cons-cons list;
it is not an extra input or a hypothesis on the public raw domain. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005 PSTRTMIncrement009 PSTRTMThresholdCountdownCode164
open PSTRSymbolicPairedArchive

def countedHeaderMachine : Machine 505 := seqMachine retainedHeaderMachine CountTwo.machine
def countedPairMachine : Machine 725 := seqMachine countedHeaderMachine pairedTwoMachine

def countedPairLeft (first second : Datum) (remaining : List Datum) : List Bool :=
  let digits := PSTRTMNatValue017.rawPayload (first :: second :: remaining).length
  (pairedDatum second).reverse ++ (pairedDatum first).reverse ++
    false :: (HeaderCopy.bank (predDigits (predDigits digits)) ++
      false :: false :: HeaderCopy.bank digits)

theorem actual_counted_pair (first second : Datum) (remaining : List Datum) :
    ∃ (trace : List (MachineState 725)) (final : MachineState 725),
      Runs countedPairMachine (encode (first :: second :: remaining)) trace final ∧
      final.Tape = Tape.mk₂ (countedPairLeft first second remaining) (rawTail remaining) ∧
      trace.length ≤ 4096 * ((encode (first :: second :: remaining)).length + 1)^2 ∧
      ∀ clock, visitedSpace countedPairMachine (encode (first :: second :: remaining)).length
        (trace.take clock) ≤ 4096 * ((encode (first :: second :: remaining)).length + 1)^2 := by
  let data := first :: second :: remaining
  let digits := PSTRTMNatValue017.rawPayload data.length
  let base := false :: HeaderCopy.bank digits
  have enough : 2 ≤ valueDigits digits := by
    simp only [digits, PSTRTMNatValue017.valueDigits_rawPayload, data, List.length_cons]
    omega
  obtain ⟨headerTrace,headerFinal,headerRun,_headerPort,headerTape,headerTime,_headerSpace⟩ :=
    actual_retained_header data
  have suffixNonempty : rawTail data ≠ [] := by simp [rawTail]
  obtain ⟨headBit,tail,suffixEq⟩ := List.exists_cons_of_ne_nil suffixNonempty
  obtain ⟨countTrace,countFinal,countRun,_countPort,_countHalt,countTape,countTime,_countSpace⟩ :=
    CountTwo.actual base digits headBit tail (encode data).length enough
  have countStart : RunsFrom CountTwo.machine ⟨0,headerFinal.Tape⟩ countTrace countFinal := by
    rw [headerTape, suffixEq]
    exact countRun
  let prefixTrace := headerTrace.map (leftCfg (b := 401)) ++ countTrace.map (rightCfg (a := 103))
  let prefixFinal := rightCfg (a := 103) countFinal
  have prefixRun : Runs countedHeaderMachine (encode data) prefixTrace prefixFinal :=
    seq_runs retainedHeaderMachine CountTwo.machine (encode data) headerFinal countFinal
      headerTrace countTrace headerRun countStart
  let archive := false :: (HeaderCopy.bank (predDigits (predDigits digits)) ++ false :: base)
  obtain ⟨pairTrace,pairFinal,pairRun,pairTape,pairTime,_pairSpace⟩ :=
    actual_two_datums archive first second (rawTail remaining)
  have rawSuffix : rawTail data = encodeDatum first ++ encodeDatum second ++ rawTail remaining := by
    simp only [data, rawTail, List.flatMap_cons, List.append_assoc]
  have pairStart : RunsFrom pairedTwoMachine ⟨0,prefixFinal.Tape⟩ pairTrace pairFinal := by
    change RunsFrom pairedTwoMachine ⟨0,countFinal.Tape⟩ pairTrace pairFinal
    rw [countTape]
    change RunsFrom pairedTwoMachine ⟨0,Tape.mk₂ archive (headBit :: tail)⟩ pairTrace pairFinal
    rw [← suffixEq, rawSuffix]
    exact pairRun
  let trace := prefixTrace.map (leftCfg (b := 219)) ++ pairTrace.map (rightCfg (a := 505))
  let final := rightCfg (a := 505) pairFinal
  have run : Runs countedPairMachine (encode data) trace final :=
    seq_runs countedHeaderMachine pairedTwoMachine (encode data) prefixFinal pairFinal
      prefixTrace pairTrace prefixRun pairStart
  have width : digits.length = natBits data.length := by
    simp only [digits, PSTRTMNatValue017.rawPayload, List.length_ofFn]
  have inputRoom : digits.length + 1 ≤ (encode data).length + 1 := by
    rw [width, PSTRTMLength004.encode_length]
    omega
  have squareRoom : (encode data).length + 1 ≤ ((encode data).length + 1)^2 := by nlinarith
  have countBound : countTrace.length ≤ 64 * ((encode data).length + 1)^2 := by omega
  have pairRoom : (encodeDatum first).length + (encodeDatum second).length + 1 ≤
      (encode data).length + 1 := by
    simp only [data, encode, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    omega
  have pairBound := pairTime.trans
    (Nat.mul_le_mul_left 256 (Nat.pow_le_pow_left pairRoom 2))
  have time : trace.length ≤ 1344 * ((encode data).length + 1)^2 := by
    simp only [trace, prefixTrace, List.length_append, List.length_map]
    omega
  refine ⟨trace,final,run,?_,?_,?_⟩
  · change pairFinal.Tape = _
    rw [pairTape]
    rfl
  · change trace.length ≤ 4096 * ((encode data).length + 1)^2
    omega
  · intro clock
    change visitedSpace countedPairMachine (encode data).length (trace.take clock) ≤
      4096 * ((encode data).length + 1)^2
    have space := PSTRTMTrace002.visitedSpace_le countedPairMachine (encode data).length (trace.take clock)
    have short := List.length_take_le' clock trace
    omega

theorem counted_pair_value (first second : Datum) (remaining : List Datum) :
    valueDigits (predDigits (predDigits (PSTRTMNatValue017.rawPayload
      (first :: second :: remaining).length))) = remaining.length := by
  have value := CountTwo.two_value (PSTRTMNatValue017.rawPayload (first :: second :: remaining).length)
    (by simp only [PSTRTMNatValue017.valueDigits_rawPayload, List.length_cons]; omega)
  rw [PSTRTMNatValue017.valueDigits_rawPayload] at value
  simp only [List.length_cons] at value ⊢
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit
