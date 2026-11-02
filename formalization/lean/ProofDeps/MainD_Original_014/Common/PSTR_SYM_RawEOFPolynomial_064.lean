module

public import Common.PSTR_SYM_OriginalRawEOF_063

/-! SOURCEONLY. Original-length budget for the SAME complete raw parser
trace. Neither a new trace nor a supplied size/fuel/EOF qualification is
introduced. The output is a paired archive, not the symbolic Expr TREE. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop

open PaperProofs.Common Turing PSTRTMIncrement009 PSTRSymbolicRawBootstrap
open PSTRSymbolicLaneArchive PSTRSymbolicCursorArchive PA17TMRatArithmeticParse002

theorem datum_pairs_bytes (value : Datum) : 2 * (datumPairs value).length = (encodeDatum value).length := by
  cases value with
  | natural number =>
    simp only [datumPairs,naturalPairs,falsePairs,List.length_append,List.length_map,List.length_singleton,
      PSTRSymbolicLocator.rawPayload_length,PSTRTMLength004.encodeDatum_natural_length]
    omega
  | rational value =>
    cases shape : denominatorDigits value with
    | nil => exact False.elim (rawPayload_nonempty value.den shape)
    | cons first later =>
      have den := denominatorDigits_length value
      rw [shape,List.length_cons] at den
      simp only [datumPairs,shape,rationalPairs,falsePairs,List.length_append,List.length_map,
        List.length_cons,List.length_nil,numeratorDigits_length,PSTRTMLength004.encodeDatum_rational_length]
      omega

theorem pairs_bytes (data : List Datum) : 2 * (allDatumPairs data).length = (data.flatMap encodeDatum).length := by
  induction data with
  | nil => rfl
  | cons value later ih =>
    have one := datum_pairs_bytes value
    change 2 * (later.flatMap datumPairs).length = (later.flatMap encodeDatum).length at ih
    simp only [allDatumPairs,List.flatMap_cons,List.length_append]
    omega

theorem count_bytes (data : List Datum) : data.length ≤ (data.flatMap encodeDatum).length := by
  induction data with
  | nil => exact Nat.zero_le 0
  | cons value later ih =>
    have positive := PSTRTMLength004.datumBits_pos value
    rw [← PSTRTMLength004.encodeDatum_length] at positive
    simp only [List.length_cons,List.flatMap_cons,List.length_append]
    omega

theorem raw_eof_time_polynomial {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool) :
    rawEOFTime input available ≤ 4096 * ((CompactPrice.symbolicInput input available).length + 1)^3 := by
  let data := rawInstance input ++ rawSet available
  let remaining := originalRemaining input available
  let size := (CompactPrice.symbolicInput input available).length
  let payload := (data.flatMap encodeDatum).length
  let pairs := (allDatumPairs data).length
  let width := (afterTwo data.length).length
  have layout : size = 2 * natBits data.length + 2 + payload := by
    change (encode data).length = _
    simp only [encode,List.length_append,PSTRTMLength004.encodeNat_length,List.length_singleton]
    omega
  have payloadRoom : payload ≤ size := by omega
  have pairSizes : 2 * pairs = payload := pairs_bytes data
  have pairsRoom : pairs ≤ size := by omega
  have countRoom : data.length ≤ size := (count_bytes data).trans payloadRoom
  have fields : data = .natural I.stageCount :: .natural I.toolCount :: remaining := rfl
  have length := congrArg List.length fields
  simp only [List.length_cons] at length
  have remainingRoom : remaining.length ≤ size := by omega
  have widthEqual : width = natBits data.length := by
    change (afterTwo data.length).length = _
    rw [(two_count_rounds data.length (PSTRSymbolicCounter.original_data_count_pos input available)).2.2.2,
      PSTRSymbolicLocator.rawPayload_length]
  have widthRoom : width ≤ size := by rw [widthEqual]; omega
  have square := Nat.pow_le_pow_left (Nat.add_le_add_right payloadRoom 1) 2
  have bodyRoom : cycleBudget pairs width payload ≤ 512 * (size + 1)^2 := by
    unfold cycleBudget
    nlinarith [Nat.zero_le (size^2)]
  have totalRoom := Nat.mul_le_mul remainingRoom bodyRoom
  change 1024 * (size + 1)^2 + remaining.length * cycleBudget pairs width payload + 1 ≤
    4096 * (size + 1)^3
  nlinarith [Nat.zero_le (size^2),Nat.zero_le (size^3)]

theorem original_raw_eof_polynomial {I : Instance} (input : StatisticalInput I) (available : Finset I.Tool)
    (positive : 0 < I.stageCount) :
    ∃ (digits : List Bool) (trace : List (MachineState loopSupport.card)) (final : MachineState loopSupport.card),
      Runs rawLoopMachine (CompactPrice.symbolicInput input available) trace final ∧
      final.Tape = archiveTape (rawInstance input ++ rawSet available) [] digits [] true ∧
      final.Tape.head = true ∧ final.Tape.right = ListBlank.mk [] ∧
      valueDigits digits = 0 ∧ 3 ≤ digits.length ∧
      trace.length ≤ 4096 * ((CompactPrice.symbolicInput input available).length + 1)^3 ∧
      ∀ clock, visitedSpace rawLoopMachine (CompactPrice.symbolicInput input available).length (trace.take clock) ≤
        16384 * ((CompactPrice.symbolicInput input available).length + 1)^3 := by
  obtain ⟨digits,trace,final,actual,tape,value,width,time,cells⟩ := original_raw_eof input available positive
  let size := (CompactPrice.symbolicInput input available).length
  have polynomial := raw_eof_time_polynomial input available
  change rawEOFTime input available ≤ 4096 * (size + 1)^3 at polynomial
  have room := (original_positive_header input available positive).1
  have inputRoom : size + 1 ≤ (size + 1)^3 := by
    nlinarith [Nat.zero_le (size^2),Nat.zero_le (size^3)]
  refine ⟨digits,trace,final,actual,tape,?_,?_,value,?_,?_,?_⟩
  · rw [tape]
    rfl
  · rw [tape]
    rfl
  · rw [width]
    exact room
  · exact time.trans polynomial
  · intro clock
    have bounded := cells clock
    change visitedSpace rawLoopMachine size (trace.take clock) ≤
      size + 2 * rawEOFTime input available + 1 at bounded
    change visitedSpace rawLoopMachine size (trace.take clock) ≤ 16384 * (size + 1)^3
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRawLoop
