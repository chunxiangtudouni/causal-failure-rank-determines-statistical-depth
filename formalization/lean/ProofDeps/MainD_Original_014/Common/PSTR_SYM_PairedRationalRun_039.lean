module

public import Common.PSTR_SYM_PairedRational_038

/-! Actual sign transfer and backward numerator rewrite for the same fixed
Rat compactor. These are preserving-code contracts, not Rat arithmetic or
an assumed complete raw parser. Denominator/entry assembly follows below. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive

open Turing PSTRTMSeq005 PSTRTMRawNat010

def signA (negative : Bool) : Fin 32 := if negative then 19 else 18
def signB (negative : Bool) : Fin 32 := if negative then 21 else 20

def signPrefix (archive : List Bool) (negative : Bool) (tail : List Bool) : List (MachineState 31) :=
  [ratState 17 archive (negative :: false :: tail),
    ratState (signA negative) archive (false :: false :: tail),
    ratState (signB negative) (false :: archive) (false :: tail),
    ratState 22 (false :: archive) (negative :: tail),
    ratState 23 archive (false :: negative :: tail),
    ratState 24 (false :: archive) (negative :: tail)]

def ratTail (numerator : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) : List Bool :=
  zeroPairs numerator ++ true :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix)

def signReturnTrace (archive : List Bool) (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) : List (MachineState 31) :=
  signPrefix archive negative (ratTail numerator firstDen laterDen suffix) ++
    numReturnTrace (negative :: false :: archive) numerator firstDen laterDen suffix

def signReturnFinal (archive : List Bool) (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) : MachineState 31 :=
  numReturnFinal (negative :: false :: archive) numerator firstDen laterDen suffix

theorem signPrefix_chain (archive : List Bool) (negative : Bool) (tail : List Bool) :
    (signPrefix archive negative tail).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  cases negative <;> simp [signPrefix, signA, signB, List.isChain_cons_cons,
    TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem signReturn_runsFrom (archive : List Bool) (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    RunsFrom rationalCompactMachine
      (ratState 17 archive (negative :: false :: ratTail numerator firstDen laterDen suffix))
      (signReturnTrace archive negative numerator firstDen laterDen suffix)
      (signReturnFinal archive negative numerator firstDen laterDen suffix) := by
  refine ⟨rfl, ?_, ?_, rationalCompact_halt _ _⟩
  · apply List.IsChain.append
    · exact signPrefix_chain _ _ _
    · exact numReturn_chain _ _ _ _ _
    · intro before beforeLast after afterHead
      simp only [signPrefix, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_some_iff] at beforeLast
      rw [numReturn_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      simp [TM0.step, rationalCompactMachine, ratState, ratTail, Tape.mk₂]
  · simp only [signReturnTrace, List.getLast?_append, numReturn_last, Option.some_or, signReturnFinal]

theorem signReturn_length (archive : List Bool) (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (signReturnTrace archive negative numerator firstDen laterDen suffix).length =
      2 * (numerator.length + laterDen.length) + 11 := by
  simp only [signReturnTrace, List.length_append, signPrefix, List.length_cons,
    List.length_nil, numReturn_length]
  omega

def numBackFront (archive : List Bool) (negative : Bool) (earlierReverse processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) : MachineState 31 :=
  match earlierReverse with
  | [] => ratState 9 (negative :: archive) (false :: ratTail processed firstDen laterDen suffix)
  | bit :: earlier => ratState 9 (bit :: (leftBlocks earlier ++ false :: negative :: archive))
      (true :: ratTail processed firstDen laterDen suffix)

def dataA (bit : Bool) : Fin 32 := if bit then 12 else 11
def dataB (bit : Bool) : Fin 32 := if bit then 14 else 13

def numBackPrefix (archive : List Bool) (negative bit : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) : List (MachineState 31) :=
  [numBackFront archive negative (bit :: earlier) processed firstDen laterDen suffix,
    ratState 10 (leftBlocks earlier ++ false :: negative :: archive)
      (bit :: true :: ratTail processed firstDen laterDen suffix),
    ratState (dataA bit) (leftBlocks earlier ++ false :: negative :: archive)
      (false :: true :: ratTail processed firstDen laterDen suffix),
    ratState (dataB bit) (false :: (leftBlocks earlier ++ false :: negative :: archive))
      (true :: ratTail processed firstDen laterDen suffix),
    ratState 15 (false :: (leftBlocks earlier ++ false :: negative :: archive))
      (bit :: ratTail processed firstDen laterDen suffix),
    ratState 16 (leftBlocks earlier ++ false :: negative :: archive)
      (false :: bit :: ratTail processed firstDen laterDen suffix)]

def numBackTrace (archive : List Bool) (negative : Bool) :
    List Bool → List Bool → Bool → List Bool → List Bool → List (MachineState 31)
  | [], processed, firstDen, laterDen, suffix =>
      [numBackFront archive negative [] processed firstDen laterDen suffix] ++
        signReturnTrace archive negative processed firstDen laterDen suffix
  | bit :: earlier, processed, firstDen, laterDen, suffix =>
      numBackPrefix archive negative bit earlier processed firstDen laterDen suffix ++
        numBackTrace archive negative earlier (bit :: processed) firstDen laterDen suffix

theorem numBack_head (archive : List Bool) (negative : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (numBackTrace archive negative earlier processed firstDen laterDen suffix).head? =
      some (numBackFront archive negative earlier processed firstDen laterDen suffix) := by
  cases earlier <;> rfl

theorem numBack_last (archive : List Bool) (negative : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (numBackTrace archive negative earlier processed firstDen laterDen suffix).getLast? =
      some (signReturnFinal archive negative (earlier.reverse ++ processed) firstDen laterDen suffix) := by
  induction earlier generalizing processed with
  | nil =>
    simp only [numBackTrace, List.getLast?_append,
      (signReturn_runsFrom archive negative processed firstDen laterDen suffix).2.2.1,
      Option.some_or, List.reverse_nil, List.nil_append]
  | cons bit earlier ih =>
    simp only [numBackTrace, numBackPrefix, List.cons_append, List.nil_append,
      List.getLast?_cons, ih, Option.getD_some, List.reverse_cons, List.append_assoc]

theorem numBack_prefix_chain (archive : List Bool) (negative bit : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (numBackPrefix archive negative bit earlier processed firstDen laterDen suffix).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  cases bit <;> simp [numBackPrefix, numBackFront, dataA, dataB, List.isChain_cons_cons,
    TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem numBack_link (archive : List Bool) (negative bit : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    TM0.step rationalCompactMachine
      (ratState 16 (leftBlocks earlier ++ false :: negative :: archive)
        (false :: bit :: ratTail processed firstDen laterDen suffix)) =
      some (numBackFront archive negative earlier (bit :: processed) firstDen laterDen suffix) := by
  cases earlier <;> simp [numBackFront, ratTail, zeroPairs_cons, leftBlocks, List.flatMap_cons,
    TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem numBack_chain (archive : List Bool) (negative : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (numBackTrace archive negative earlier processed firstDen laterDen suffix).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  induction earlier generalizing processed with
  | nil =>
    apply List.IsChain.append
    · exact .singleton _
    · exact (signReturn_runsFrom archive negative processed firstDen laterDen suffix).2.1
    · intro before beforeLast after afterHead
      simp only [List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [(signReturn_runsFrom archive negative processed firstDen laterDen suffix).1] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      simp [numBackFront, TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
  | cons bit earlier ih =>
    apply List.IsChain.append
    · exact numBack_prefix_chain _ _ _ _ _ _ _ _
    · exact ih _
    · intro before beforeLast after afterHead
      simp only [numBackPrefix, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_some_iff] at beforeLast
      rw [numBack_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      exact numBack_link _ _ _ _ _ _ _ _

theorem numBack_runsFrom (archive : List Bool) (negative : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    RunsFrom rationalCompactMachine (numBackFront archive negative earlier processed firstDen laterDen suffix)
      (numBackTrace archive negative earlier processed firstDen laterDen suffix)
      (signReturnFinal archive negative (earlier.reverse ++ processed) firstDen laterDen suffix) :=
  ⟨numBack_head _ _ _ _ _ _ _, numBack_chain _ _ _ _ _ _ _, numBack_last _ _ _ _ _ _ _,
    rationalCompact_halt _ _⟩

theorem numBack_length (archive : List Bool) (negative : Bool) (earlier processed : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (numBackTrace archive negative earlier processed firstDen laterDen suffix).length =
      8 * earlier.length + 2 * (processed.length + laterDen.length) + 12 := by
  induction earlier generalizing processed with
  | nil =>
    simp only [numBackTrace, List.length_append, List.length_cons, List.length_nil, signReturn_length]
    omega
  | cons bit earlier ih =>
    simp only [numBackTrace, List.length_append, numBackPrefix, List.length_cons,
      List.length_nil, ih]
    omega

/-! The denominator backward scan reuses the same fixed code. Its entry
retains the last denominator flag; the numerator and the arbitrary external
archive are still the actual parsed tape, not additional input fields. -/

def pairedRationalWord (negative : Bool) (numerator : List Bool) : List Bool → List Bool
  | [] => []
  | first :: later => rationalWord negative numerator first later

def ratArchiveFinal (archive : List Bool) (negative : Bool) (numerator denominator suffix : List Bool) :
    MachineState 31 :=
  ratState 31 ((pairedRationalWord negative numerator denominator).reverse ++ archive) suffix

theorem signReturn_whole_final (archive : List Bool) (negative : Bool) (numerator : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    signReturnFinal archive negative numerator firstDen laterDen suffix =
      ratArchiveFinal archive negative numerator (firstDen :: laterDen) suffix := by
  simp [signReturnFinal, numReturnFinal, denReturnFinal, ratArchiveFinal,
    pairedRationalWord, rationalWord, List.reverse_append, List.reverse_cons, List.append_assoc]

def numParsedLeft (archive : List Bool) (negative : Bool) (numReverse : List Bool) : List Bool :=
  leftBlocks numReverse ++ false :: negative :: archive

def denBackFront (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (earlierDen : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) : MachineState 31 :=
  match earlierDen with
  | [] => ratState 5 (numParsedLeft archive negative numReverse)
      (false :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix))
  | bit :: earlier => ratState 5
      (bit :: (leftBlocks earlier ++ false :: numParsedLeft archive negative numReverse))
      (true :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix))

def denBackPrefix (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (bit : Bool) (earlier : List Bool) (firstDen : Bool) (laterDen suffix : List Bool) :
    List (MachineState 31) :=
  [denBackFront archive negative numReverse (bit :: earlier) firstDen laterDen suffix,
    ratState 6 (bit :: (leftBlocks earlier ++ false :: numParsedLeft archive negative numReverse))
      (false :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix)),
    ratState 7 (leftBlocks earlier ++ false :: numParsedLeft archive negative numReverse)
      (bit :: false :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix))]

def denBackTrace (archive : List Bool) (negative : Bool) (numReverse : List Bool) :
    List Bool → Bool → List Bool → List Bool → List (MachineState 31)
  | [], firstDen, laterDen, suffix =>
      [denBackFront archive negative numReverse [] firstDen laterDen suffix,
        ratState 8 (numParsedLeft archive negative numReverse)
          (true :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix))] ++
        numBackTrace archive negative numReverse [] firstDen laterDen suffix
  | bit :: earlier, firstDen, laterDen, suffix =>
      denBackPrefix archive negative numReverse bit earlier firstDen laterDen suffix ++
        denBackTrace archive negative numReverse earlier bit (firstDen :: laterDen) suffix

theorem denBack_head (archive : List Bool) (negative : Bool) (numReverse earlier : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (denBackTrace archive negative numReverse earlier firstDen laterDen suffix).head? =
      some (denBackFront archive negative numReverse earlier firstDen laterDen suffix) := by
  cases earlier <;> rfl

theorem denBack_last (archive : List Bool) (negative : Bool) (numReverse earlier : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (denBackTrace archive negative numReverse earlier firstDen laterDen suffix).getLast? =
      some (ratArchiveFinal archive negative numReverse.reverse
        (earlier.reverse ++ firstDen :: laterDen) suffix) := by
  induction earlier generalizing firstDen laterDen with
  | nil =>
    simp only [denBackTrace, List.getLast?_append, numBack_last, Option.some_or,
      List.append_nil, signReturn_whole_final, List.reverse_nil, List.nil_append]
  | cons bit earlier ih =>
    simp only [denBackTrace, denBackPrefix, List.cons_append, List.nil_append,
      List.getLast?_cons, ih, Option.getD_some, List.reverse_cons, List.append_assoc]

theorem denBack_prefix_chain (archive : List Bool) (negative : Bool) (numReverse earlier : List Bool)
    (bit firstDen : Bool) (laterDen suffix : List Bool) :
    (denBackPrefix archive negative numReverse bit earlier firstDen laterDen suffix).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  simp [denBackPrefix, denBackFront, List.isChain_cons_cons,
    TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem denBack_link (archive : List Bool) (negative : Bool) (numReverse earlier : List Bool)
    (bit firstDen : Bool) (laterDen suffix : List Bool) :
    TM0.step rationalCompactMachine
      (ratState 7 (leftBlocks earlier ++ false :: numParsedLeft archive negative numReverse)
        (bit :: false :: firstDen :: (zeroPairs laterDen ++ true :: true :: suffix))) =
      some (denBackFront archive negative numReverse earlier bit (firstDen :: laterDen) suffix) := by
  cases earlier <;> simp [denBackFront, zeroPairs_cons, leftBlocks, List.flatMap_cons,
    TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem denBack_chain (archive : List Bool) (negative : Bool) (numReverse earlier : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (denBackTrace archive negative numReverse earlier firstDen laterDen suffix).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  induction earlier generalizing firstDen laterDen with
  | nil =>
    apply List.IsChain.append
    · simp [denBackFront, List.isChain_cons_cons, TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
    · exact numBack_chain _ _ _ _ _ _ _
    · intro before beforeLast after afterHead
      simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.mem_some_iff] at beforeLast
      rw [numBack_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      cases numReverse <;> simp [numParsedLeft, numBackFront, ratTail, zeroPairs,
        leftBlocks, List.flatMap_cons, TM0.step, rationalCompactMachine, ratState, Tape.mk₂]
  | cons bit earlier ih =>
    apply List.IsChain.append
    · exact denBack_prefix_chain _ _ _ _ _ _ _ _
    · exact ih _ _
    · intro before beforeLast after afterHead
      simp only [denBackPrefix, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_some_iff] at beforeLast
      rw [denBack_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      exact denBack_link _ _ _ _ _ _ _ _

theorem denBack_length (archive : List Bool) (negative : Bool) (numReverse earlier : List Bool)
    (firstDen : Bool) (laterDen suffix : List Bool) :
    (denBackTrace archive negative numReverse earlier firstDen laterDen suffix).length =
      8 * numReverse.length + 5 * earlier.length + 2 * laterDen.length + 14 := by
  induction earlier generalizing firstDen laterDen with
  | nil =>
    simp only [denBackTrace, List.length_append, List.length_cons, List.length_nil, numBack_length]
    omega
  | cons bit earlier ih =>
    simp only [denBackTrace, List.length_append, denBackPrefix, List.length_cons, List.length_nil, ih]
    omega

/-! Five charged operations enter the proved backward run from the exact
parsed Rat cursor. The old denominator END becomes the Rat type bit. -/

def ratEntryPrefix (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (last : Bool) (earlier suffix : List Bool) : List (MachineState 31) :=
  [ratState 0 (false :: (leftBlocks (last :: earlier) ++ false :: numParsedLeft archive negative numReverse)) suffix,
    ratState 1 (leftBlocks (last :: earlier) ++ false :: numParsedLeft archive negative numReverse) (false :: suffix),
    ratState 2 (leftBlocks (last :: earlier) ++ false :: numParsedLeft archive negative numReverse) (true :: suffix),
    ratState 3 (last :: (leftBlocks earlier ++ false :: numParsedLeft archive negative numReverse)) (true :: true :: suffix),
    ratState 4 (leftBlocks earlier ++ false :: numParsedLeft archive negative numReverse) (last :: true :: true :: suffix)]

def ratCompactTrace (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (last : Bool) (earlier suffix : List Bool) : List (MachineState 31) :=
  ratEntryPrefix archive negative numReverse last earlier suffix ++
    denBackTrace archive negative numReverse earlier last [] suffix

theorem ratEntry_chain (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (last : Bool) (earlier suffix : List Bool) :
    (ratEntryPrefix archive negative numReverse last earlier suffix).IsChain
      (fun before after => TM0.step rationalCompactMachine before = some after) := by
  simp [ratEntryPrefix, List.isChain_cons_cons, leftBlocks, List.flatMap_cons,
    TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem ratEntry_link (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (last : Bool) (earlier suffix : List Bool) :
    TM0.step rationalCompactMachine
      (ratState 4 (leftBlocks earlier ++ false :: numParsedLeft archive negative numReverse)
        (last :: true :: true :: suffix)) =
      some (denBackFront archive negative numReverse earlier last [] suffix) := by
  cases earlier <;> simp [denBackFront, zeroPairs, leftBlocks, List.flatMap_cons,
    TM0.step, rationalCompactMachine, ratState, Tape.mk₂]

theorem ratCompact_runsFrom (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (last : Bool) (earlier suffix : List Bool) :
    RunsFrom rationalCompactMachine
      (ratState 0 (false :: (leftBlocks (last :: earlier) ++ false :: numParsedLeft archive negative numReverse)) suffix)
      (ratCompactTrace archive negative numReverse last earlier suffix)
      (ratArchiveFinal archive negative numReverse.reverse (earlier.reverse ++ [last]) suffix) := by
  refine ⟨rfl, ?_, ?_, rationalCompact_halt _ _⟩
  · apply List.IsChain.append
    · exact ratEntry_chain _ _ _ _ _ _
    · exact denBack_chain _ _ _ _ _ _ _
    · intro before beforeLast after afterHead
      simp only [ratEntryPrefix, List.getLast?_cons_cons, List.getLast?_singleton,
        Option.mem_some_iff] at beforeLast
      rw [denBack_head] at afterHead
      have same := Option.mem_some_iff.mp afterHead
      subst before
      subst after
      exact ratEntry_link _ _ _ _ _ _
  · simp only [ratCompactTrace, List.getLast?_append, denBack_last, Option.some_or]

theorem ratCompact_length (archive : List Bool) (negative : Bool) (numReverse : List Bool)
    (last : Bool) (earlier suffix : List Bool) :
    (ratCompactTrace archive negative numReverse last earlier suffix).length =
      8 * numReverse.length + 5 * earlier.length + 19 := by
  simp only [ratCompactTrace, List.length_append, ratEntryPrefix, List.length_cons,
    List.length_nil, denBack_length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicPairedArchive
