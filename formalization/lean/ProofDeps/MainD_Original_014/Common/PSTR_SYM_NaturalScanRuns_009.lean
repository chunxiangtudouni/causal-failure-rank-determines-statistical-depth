module

public import Common.PSTR_SYM_NaturalScan_008

/-! The dynamic Natural-Datum loop has an actual single trace. Every jump
into the fixed parser and every parser-HALT-to-test transfer is charged. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

open Turing PA17TMRatArithmeticParse002

theorem scanTrace_last (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (scanTrace left numbers suffix).getLast? = some (scanFinal left numbers suffix) := by
  induction numbers generalizing left with
  | nil => rfl
  | cons number later ih =>
    have nonempty := List.append_ne_nil_of_right_ne_nil
      ((streamTrace (false :: left) [] (PSTRTMNatValue017.rawPayload number)
        (naturalPrefix later ++ true :: suffix)).map embedCfg)
      (scanTrace_nonempty (naturalLeft left number) later suffix)
    rw [scanTrace, List.getLast?_cons_of_ne_nil nonempty, List.getLast?_append, ih, Option.some_or]
    all_goals rfl

/-- TRUE is a real next tag, not an assumed EOF. The local contract states
which TRUE tag is present; later callers must handle the original N0 branch. -/
theorem scan_runsFrom (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom scanMachine
      (scanState 0 left (naturalPrefix numbers ++ true :: suffix))
      (scanTrace left numbers suffix) (scanFinal left numbers suffix) := by
  induction numbers generalizing left with
  | nil => exact ⟨rfl, .singleton _, rfl, scan_true_halt left suffix⟩
  | cons number later ih =>
    have parsed := encodeNat_stream_runsFrom (false :: left)
      (naturalPrefix later ++ true :: suffix) number
    have continuation := ih (naturalLeft left number)
    have parsedChain : ((streamTrace (false :: left) [] (PSTRTMNatValue017.rawPayload number)
        (naturalPrefix later ++ true :: suffix)).map embedCfg).IsChain
        (fun before after => TM0.step scanMachine before = some after) := by
      apply (List.isChain_map _).mpr
      apply parsed.2.1.imp
      intro before after actual
      rw [scan_step_embed, actual]
    have joined := parsedChain.append continuation.2.1 (by
      intro before beforeLast after afterFirst
      simp only [List.getLast?_map, parsed.2.2.1, Option.map_some, Option.mem_some_iff] at beforeLast
      simp only [scanTrace_head, Option.mem_some_iff] at afterFirst
      subst before
      subst after
      rw [scan_step_embed, parsed.2.2.2]
      all_goals rfl)
    refine ⟨scanTrace_head left (number :: later) suffix, ?_,
      scanTrace_last left (number :: later) suffix, scan_true_halt _ _⟩
    change List.IsChain _ (scanState 0 left
      (encodeDatum (.natural number) ++ naturalPrefix later ++ true :: suffix) :: _)
    apply List.isChain_cons.mpr
    constructor
    · intro after afterFirst
      simp only [List.head?_append, List.head?_map, parsed.1,
        Option.map_some, Option.some_or, Option.mem_some_iff] at afterFirst
      subst after
      simpa only [encodeDatum, List.cons_append, List.append_assoc] using
        scan_false_step left (encodeNat number ++ naturalPrefix later ++ true :: suffix)
    · exact joined

theorem rawPayload_length (number : Nat) :
    (PSTRTMNatValue017.rawPayload number).length = natBits number := by
  simp only [PSTRTMNatValue017.rawPayload, List.length_ofFn]

theorem scanTrace_length (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (scanTrace left numbers suffix).length =
      1 + (numbers.map (fun number => (natBits number)^2 + 9 * natBits number + 3)).sum := by
  induction numbers generalizing left with
  | nil => rfl
  | cons number later ih =>
    simp only [scanTrace, List.length_cons, List.length_append, List.length_map,
      streamTrace_length, rawPayload_length, ih, List.map_cons, List.sum_cons]
    omega

/-- A polynomial bound on the SAME actual trace, in the actual consumed
Natural prefix length. Numeric Rat values are never made unary. -/
theorem scan_time_le (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    (scanTrace left numbers suffix).length ≤ 16 * ((naturalPrefix numbers).length + 1)^2 := by
  induction numbers generalizing left with
  | nil => change 1 ≤ 16; decide
  | cons number later ih =>
    have previous := ih (naturalLeft left number)
    have count : (scanTrace left (number :: later) suffix).length =
        (natBits number)^2 + 9 * natBits number + 3 +
          (scanTrace (naturalLeft left number) later suffix).length := by
      simp only [scanTrace, List.length_cons, List.length_append, List.length_map,
        streamTrace_length, rawPayload_length]
      omega
    have field : (naturalPrefix (number :: later)).length =
        2 * natBits number + 2 + (naturalPrefix later).length := by
      rw [naturalPrefix_cons, List.length_append, PSTRTMLength004.encodeDatum_natural_length]
    rw [count, field]
    nlinarith [Nat.zero_le ((naturalPrefix later).length * natBits number)]

theorem scan_space_le (inputLength : Nat) (left : List Bool) (numbers : List Nat) (suffix : List Bool) :
    visitedSpace scanMachine inputLength (scanTrace left numbers suffix) ≤
      inputLength + 32 * ((naturalPrefix numbers).length + 1)^2 + 1 := by
  have cells := PSTRTMTrace002.visitedSpace_le scanMachine inputLength (scanTrace left numbers suffix)
  have clock := scan_time_le left numbers suffix
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator
