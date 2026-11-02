module

public import Common.PSTR_SYM_PairedNaturalForward_036

/-! Actual backward flag-clearing phase, followed by the real036 return.
Payload bits are preserved. This is still an internal phase entry, not an
assertion that the full original raw parser has reached this configuration. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive

open Turing PSTRTMSeq005 PSTRTMRawNat010

def backwardFront (archive : List Bool) (earlierReverse : List Bool)
    (first : Bool) (later suffix : List Bool) : MachineState 11 :=
  match earlierReverse with
  | [] => state 4 archive (naturalWord (first :: later) ++ suffix)
  | bit :: earlier => state 4 (bit :: (leftBlocks earlier ++ false :: archive))
      (true :: first :: (naturalWord later ++ suffix))

def backwardPrefix (archive : List Bool) (bit : Bool) (earlier : List Bool)
    (first : Bool) (later suffix : List Bool) : List (MachineState 11) :=
  [backwardFront archive (bit :: earlier) first later suffix,
    state 5 (bit :: (leftBlocks earlier ++ false :: archive))
      (false :: first :: (naturalWord later ++ suffix)),
    state 6 (leftBlocks earlier ++ false :: archive)
      (bit :: false :: first :: (naturalWord later ++ suffix))]

def backwardTrace (archive : List Bool) :
    List Bool → Bool → List Bool → List Bool → List (MachineState 11)
  | [], first, later, suffix => finishTrace archive first later suffix
  | bit :: earlier, first, later, suffix =>
      backwardPrefix archive bit earlier first later suffix ++
        backwardTrace archive earlier bit (first :: later) suffix

theorem backward_head (archive earlier : List Bool) (first : Bool) (later suffix : List Bool) :
    (backwardTrace archive earlier first later suffix).head? =
      some (backwardFront archive earlier first later suffix) := by
  cases earlier with
  | nil => exact (finish_runsFrom archive first later suffix).1
  | cons bit earlier => rfl

theorem backward_last (archive earlier : List Bool) (first : Bool) (later suffix : List Bool) :
    (backwardTrace archive earlier first later suffix).getLast? =
      some (forwardFinal archive (earlier.reverse ++ first :: later) suffix) := by
  induction earlier generalizing first later with
  | nil => exact (finish_runsFrom archive first later suffix).2.2.1
  | cons bit earlier ih =>
    simp only [backwardTrace, backwardPrefix, List.cons_append, List.nil_append,
      List.getLast?_cons, ih, Option.getD_some, List.reverse_cons, List.append_assoc]

theorem backward_prefix_chain (archive earlier : List Bool) (bit first : Bool) (later suffix : List Bool) :
    (backwardPrefix archive bit earlier first later suffix).IsChain
      (fun before after => TM0.step naturalCompactMachine before = some after) := by
  simp [backwardPrefix, backwardFront, List.isChain_cons_cons, TM0.step,
    naturalCompactMachine, state, Tape.mk₂]

theorem backward_link (archive earlier : List Bool) (bit first : Bool) (later suffix : List Bool) :
    TM0.step naturalCompactMachine
      (state 6 (leftBlocks earlier ++ false :: archive)
        (bit :: false :: first :: (naturalWord later ++ suffix))) =
      some (backwardFront archive earlier bit (first :: later) suffix) := by
  cases earlier with
  | nil =>
    simp [backwardFront, naturalWord_cons, leftBlocks, TM0.step,
      naturalCompactMachine, state, Tape.mk₂]
  | cons older earlier =>
    simp [backwardFront, naturalWord_cons, leftBlocks, List.flatMap_cons,
      TM0.step, naturalCompactMachine, state, Tape.mk₂]

theorem backward_chain (archive earlier : List Bool) (first : Bool) (later suffix : List Bool) :
    (backwardTrace archive earlier first later suffix).IsChain
      (fun before after => TM0.step naturalCompactMachine before = some after) := by
  induction earlier generalizing first later with
  | nil => exact (finish_runsFrom archive first later suffix).2.1
  | cons bit earlier ih =>
    apply List.IsChain.append
    · exact backward_prefix_chain _ _ _ _ _ _
    · exact ih _ _
    · intro before beforeLast after afterHead
      simp only [backwardPrefix, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_some_iff] at beforeLast
      rw [backward_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      exact backward_link archive earlier bit first later suffix

theorem backward_runsFrom (archive earlier : List Bool) (first : Bool) (later suffix : List Bool) :
    RunsFrom naturalCompactMachine (backwardFront archive earlier first later suffix)
      (backwardTrace archive earlier first later suffix)
      (forwardFinal archive (earlier.reverse ++ first :: later) suffix) :=
  ⟨backward_head _ _ _ _ _, backward_chain _ _ _ _ _, backward_last _ _ _ _ _,
    naturalCompact_halt _ _⟩

theorem backward_length (archive earlier : List Bool) (first : Bool) (later suffix : List Bool) :
    (backwardTrace archive earlier first later suffix).length =
      5 * earlier.length + 2 * later.length + 5 := by
  induction earlier generalizing first later with
  | nil =>
    simpa only [backwardTrace, List.length_nil, Nat.mul_zero, Nat.zero_add] using
      finish_length archive first later suffix
  | cons bit earlier ih =>
    simp only [backwardTrace, List.length_append, backwardPrefix,
      List.length_cons, List.length_nil, ih]
    omega

/-! The genuine parsed-field entry and complete compaction. Four actual
LEFTs enter the proved backward phase; no suffix/head reset is inserted. -/

def compactEntryPrefix (archive : List Bool) (last : Bool) (earlier suffix : List Bool) :
    List (MachineState 11) :=
  [state 0 (false :: (leftBlocks (last :: earlier) ++ false :: archive)) suffix,
    state 1 (leftBlocks (last :: earlier) ++ false :: archive) (false :: suffix),
    state 2 (last :: (leftBlocks earlier ++ false :: archive)) (true :: false :: suffix),
    state 3 (leftBlocks earlier ++ false :: archive) (last :: true :: false :: suffix)]

def compactTrace (archive : List Bool) (last : Bool) (earlier suffix : List Bool) :
    List (MachineState 11) :=
  compactEntryPrefix archive last earlier suffix ++ backwardTrace archive earlier last [] suffix

theorem compactEntry_chain (archive : List Bool) (last : Bool) (earlier suffix : List Bool) :
    (compactEntryPrefix archive last earlier suffix).IsChain
      (fun before after => TM0.step naturalCompactMachine before = some after) := by
  simp [compactEntryPrefix, List.isChain_cons_cons, leftBlocks, List.flatMap_cons,
    TM0.step, naturalCompactMachine, state, Tape.mk₂]

theorem compactEntry_link (archive : List Bool) (last : Bool) (earlier suffix : List Bool) :
    TM0.step naturalCompactMachine
      (state 3 (leftBlocks earlier ++ false :: archive) (last :: true :: false :: suffix)) =
      some (backwardFront archive earlier last [] suffix) := by
  cases earlier with
  | nil =>
    simp [backwardFront, naturalWord, leftBlocks,
      TM0.step, naturalCompactMachine, state, Tape.mk₂]
  | cons bit earlier =>
    simp [backwardFront, naturalWord, leftBlocks, List.flatMap_cons,
      TM0.step, naturalCompactMachine, state, Tape.mk₂]

theorem compact_runsFrom (archive : List Bool) (last : Bool) (earlier suffix : List Bool) :
    RunsFrom naturalCompactMachine
      (state 0 (false :: (leftBlocks (last :: earlier) ++ false :: archive)) suffix)
      (compactTrace archive last earlier suffix)
      (forwardFinal archive (earlier.reverse ++ [last]) suffix) := by
  refine ⟨rfl, ?_, ?_, naturalCompact_halt _ _⟩
  · apply List.IsChain.append
    · exact compactEntry_chain _ _ _ _
    · exact backward_chain _ _ _ _ _
    · intro before beforeLast after afterHead
      simp only [compactEntryPrefix, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_some_iff] at beforeLast
      rw [backward_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      exact compactEntry_link _ _ _ _
  · simp only [compactTrace, List.getLast?_append, backward_last, Option.some_or]

theorem compact_length (archive : List Bool) (last : Bool) (earlier suffix : List Bool) :
    (compactTrace archive last earlier suffix).length = 5 * earlier.length + 9 := by
  simp only [compactTrace, List.length_append, compactEntryPrefix, List.length_cons,
    List.length_nil, backward_length]
  omega

/-! Same actual raw Natural parser followed by the same actual compactor.
The machine is constant before number/archive/suffix. The actual prefix
resource bound uses the charged full input length chosen by its caller. -/

open PSTRSymbolicDatumParser
open PSTRSymbolicLocator (naturalLeft rawPayload_length)

def naturalParseCompactMachine : Machine 30 := seqMachine naturalDatumMachine naturalCompactMachine

theorem raw_natural_parse_compact (archive : List Bool) (number : Nat) (suffix : List Bool) :
    ∃ (trace : List (MachineState 30)) (final : MachineState 30),
      RunsFrom naturalParseCompactMachine ⟨0,Tape.mk₂ archive (encodeDatum (.natural number) ++ suffix)⟩
        trace final ∧
      final.Tape = Tape.mk₂ ((naturalWord (PSTRTMNatValue017.rawPayload number)).reverse ++ archive) suffix ∧
      trace.length ≤ 32 * (natBits number + 1)^2 ∧
      ∀ inputLength clock, visitedSpace naturalParseCompactMachine inputLength (trace.take clock) ≤
        inputLength + 64 * (natBits number + 1)^2 + 1 := by
  obtain ⟨last, earlier, shape⟩ := PSTRSymbolicZeroTail.count_reverse_cons number
  have reverseShape : PSTRTMNatValue017.rawPayload number = earlier.reverse ++ [last] := by
    simpa only [List.reverse_reverse, List.reverse_cons] using congrArg List.reverse shape
  have width : natBits number = earlier.length + 1 := by
    simpa only [List.length_reverse, rawPayload_length, List.length_cons] using congrArg List.length shape
  have next : RunsFrom naturalCompactMachine ⟨0,(naturalDatumFinal archive number suffix).Tape⟩
      (compactTrace archive last earlier suffix) (forwardFinal archive (earlier.reverse ++ [last]) suffix) := by
    rw [naturalDatum_final_tape]
    change RunsFrom naturalCompactMachine
      (state 0 (false :: (leftBlocks (PSTRTMNatValue017.rawPayload number).reverse ++ false :: archive)) suffix) _ _
    rw [shape]
    exact compact_runsFrom archive last earlier suffix
  let trace := (naturalDatumTrace archive number suffix).map (leftCfg (b := 11)) ++
    (compactTrace archive last earlier suffix).map (rightCfg (a := 18))
  let final : MachineState 30 := rightCfg (a := 18)
    (forwardFinal archive (earlier.reverse ++ [last]) suffix)
  have actual : RunsFrom naturalParseCompactMachine
      ⟨0,Tape.mk₂ archive (encodeDatum (.natural number) ++ suffix)⟩ trace final :=
    seq_runsFrom naturalDatumMachine naturalCompactMachine _
      (naturalDatumFinal archive number suffix) _ _ _
      (naturalDatum_runsFrom archive number suffix) next
  have parsing := naturalDatum_time_le archive number suffix
  have compactClock : (compactTrace archive last earlier suffix).length = 5 * natBits number + 4 := by
    rw [compact_length]
    omega
  have clock : trace.length ≤ 17 * (natBits number + 1)^2 + 5 * natBits number + 4 := by
    simp only [trace, List.length_append, List.length_map]
    calc
      _ ≤ 17 * (natBits number + 1)^2 + (5 * natBits number + 4) :=
        Nat.add_le_add parsing compactClock.le
      _ = _ := by omega
  have total : trace.length ≤ 32 * (natBits number + 1)^2 := by
    calc
      _ ≤ 17 * (natBits number + 1)^2 + 5 * natBits number + 4 := clock
      _ ≤ 32 * (natBits number + 1)^2 := by
        nlinarith [Nat.zero_le (natBits number), Nat.zero_le ((natBits number)^2)]
  refine ⟨trace, final, actual, ?_, total, ?_⟩
  · change (forwardFinal archive (earlier.reverse ++ [last]) suffix).Tape = _
    rw [← reverseShape]
    rfl
  · intro inputLength tick
    have cells := PSTRTMTrace002.visitedSpace_le naturalParseCompactMachine inputLength (trace.take tick)
    have takeLength : (trace.take tick).length ≤ trace.length := by
      simp only [List.length_take]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive
