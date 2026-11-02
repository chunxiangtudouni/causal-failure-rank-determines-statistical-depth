module
public import Common.PSTR_TM_AlignShift_031

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAlignUnit032
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMAlignCode030 PSTRTMAlignShift031 PSTRTMTrace002

private theorem nextPhase_one : nextPhase (1 : Fin 3) = 0 := by decide
private theorem nextPhase_two : nextPhase (2 : Fin 3) = 1 := by decide

def frontierLeft (a : Bool) (left previous : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks previous ++ false :: a :: left

def markTrace (a bit : Bool) (left digits suffix : List Bool) : List (MachineState 134) :=
  [state 0 left (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix)),
    state 1 (a :: left) (true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix)),
    state 2 (a :: left) (false :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix))]

theorem mark_chain (a bit : Bool) (left digits suffix : List Bool) :
    (markTrace a bit left digits suffix).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  simp [markTrace, List.isChain_cons_cons, Turing.TM0.step, alignMachine, state, Turing.Tape.mk₂]

def seekTrace (bit a : Bool) (left previous : List Bool) : List Bool → List Bool → List (MachineState 134)
  | [], suffix =>
    let context := frontierLeft a left previous
    [state 3 context (false :: false :: true :: false :: bit :: true :: suffix),
      state 4 (false :: context) (false :: true :: false :: bit :: true :: suffix),
      state 5 (false :: false :: context) (true :: false :: bit :: true :: suffix),
      state 6 (true :: false :: false :: context) (false :: bit :: true :: suffix),
      state 7 (false :: true :: false :: false :: context) (bit :: true :: suffix),
      state (checkB bit) (bit :: false :: true :: false :: false :: context) (true :: suffix)]
  | digit :: later, suffix =>
    let context := frontierLeft a left previous
    state 3 context (digit :: true :: (PSTRTMIncrement009.blocks later ++ false :: false :: true :: false :: bit :: true :: suffix)) ::
    state 4 (digit :: context) (true :: (PSTRTMIncrement009.blocks later ++ false :: false :: true :: false :: bit :: true :: suffix)) ::
      seekTrace bit a left (digit :: previous) later suffix

theorem seek_head (bit a : Bool) (left previous digits suffix : List Bool) :
    (seekTrace bit a left previous digits suffix).head? = some
      (state 3 (frontierLeft a left previous)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix)) := by
  cases digits <;> rfl

theorem seek_length (bit a : Bool) (left previous digits suffix : List Bool) :
    (seekTrace bit a left previous digits suffix).length = 2 * digits.length + 6 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons digit later ih =>
    simp only [seekTrace, List.length_cons, ih]
    omega

theorem seek_last (bit a : Bool) (left previous digits suffix : List Bool) :
    (seekTrace bit a left previous digits suffix).getLast? = some
      (state (checkB bit) (bit :: false :: true :: false :: false ::
        frontierLeft a left (digits.reverse ++ previous)) (true :: suffix)) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons digit later ih =>
    have hne : seekTrace bit a left (digit :: previous) later suffix ≠ [] := by
      have hh := seek_head bit a left (digit :: previous) later suffix
      intro h
      simp [h] at hh
    simp only [seekTrace, List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne, ih]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

set_option maxHeartbeats 800000 in
theorem seek_chain (bit a : Bool) (left previous digits suffix : List Bool) :
    (seekTrace bit a left previous digits suffix).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  induction digits generalizing previous with
  | nil => cases bit <;> simp [seekTrace, List.isChain_cons_cons, Turing.TM0.step, alignMachine, state, checkB, Turing.Tape.mk₂]
  | cons digit later ih =>
    rw [seekTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step, alignMachine, state, Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro next hn
      rw [seek_head] at hn
      have he := Option.mem_some_iff.mp hn
      subst next
      simp [Turing.TM0.step, alignMachine, state, Turing.Tape.mk₂,
        frontierLeft, PSTRTMRawNat010.leftBlocks]
    · exact ih _

private theorem append_link (xs ys : List (MachineState 134)) (last first : MachineState 134)
    (hx : xs.IsChain (fun a b => Turing.TM0.step alignMachine a = some b))
    (hy : ys.IsChain (fun a b => Turing.TM0.step alignMachine a = some b))
    (hl : xs.getLast? = some last) (hh : ys.head? = some first)
    (hs : Turing.TM0.step alignMachine last = some first) :
    (xs ++ ys).IsChain (fun a b => Turing.TM0.step alignMachine a = some b) := by
  apply hx.append hy
  intro a ha b hb
  rw [hl] at ha
  rw [hh] at hb
  have he := Option.mem_some_iff.mp ha
  have hf := Option.mem_some_iff.mp hb
  subst a
  subst b
  exact hs

def separateTrace (bit a : Bool) (left previous suffix : List Bool) : List (MachineState 134) :=
  let context := frontierLeft a left previous
  shiftTrace 2 bit false true (false :: false :: context) bit true suffix ++
    (shiftTrace 1 bit false false context true false (true :: false :: suffix) ++
      holeTrace bit a left previous false false (false :: false :: true :: false :: suffix))

theorem separate_head (bit a : Bool) (left previous suffix : List Bool) :
    (separateTrace bit a left previous suffix).head? = some
      (state (hole 2 bit) (false :: true :: false :: false :: frontierLeft a left previous) (bit :: true :: suffix)) := by
  simp [separateTrace, List.head?_append, shift_head]

theorem separate_length (bit a : Bool) (left previous suffix : List Bool) :
    (separateTrace bit a left previous suffix).length = 10 * previous.length + 28 := by
  simp only [separateTrace, List.length_append, shift_length, hole_length]
  omega

theorem separate_last (bit a : Bool) (left previous suffix : List Bool) :
    (separateTrace bit a left previous suffix).getLast? = some
      (state 134 (true :: bit :: true :: a :: left)
        (PSTRTMIncrement009.blocks previous.reverse ++ false :: false :: true :: false :: suffix)) := by
  simp [separateTrace, List.getLast?_append, hole_last]

theorem separate_chain (bit a : Bool) (left previous suffix : List Bool) :
    (separateTrace bit a left previous suffix).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  let context := frontierLeft a left previous
  have htail := append_link
    (shiftTrace 1 bit false false context true false (true :: false :: suffix))
    (holeTrace bit a left previous false false (false :: false :: true :: false :: suffix)) _ _
    (shift_chain 1 bit false false context true false (true :: false :: suffix) (Or.inl (by decide)))
    (hole_chain bit a left previous false false (false :: false :: true :: false :: suffix))
    (shift_last 1 bit false false context true false (true :: false :: suffix))
    (hole_head bit a left previous false false (false :: false :: true :: false :: suffix))
    (by simpa only [nextPhase_one, context, frontierLeft] using
      shift_advance 1 bit false false context (true :: false :: suffix))
  have hhead : (shiftTrace 1 bit false false context true false (true :: false :: suffix) ++
      holeTrace bit a left previous false false (false :: false :: true :: false :: suffix)).head? = some
        (state (hole 1 bit) (false :: false :: context) (true :: false :: true :: false :: suffix)) := by
    simp [List.head?_append, shift_head]
  apply append_link _ _ _ _
    (shift_chain 2 bit false true (false :: false :: context) bit true suffix (Or.inl (by decide)))
    htail (shift_last 2 bit false true (false :: false :: context) bit true suffix) hhead
  simpa only [nextPhase_two] using shift_advance 2 bit false true (false :: false :: context) suffix

def alignTrace (a bit : Bool) (left digits suffix : List Bool) : List (MachineState 134) :=
  markTrace a bit left digits suffix ++
    (seekTrace bit a left [] digits suffix ++ separateTrace bit a left digits.reverse suffix)

theorem align_head (a bit : Bool) (left digits suffix : List Bool) :
    (alignTrace a bit left digits suffix).head? = some
      (state 0 left (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix))) := rfl

theorem align_length (a bit : Bool) (left digits suffix : List Bool) :
    (alignTrace a bit left digits suffix).length = 12 * digits.length + 37 := by
  simp only [alignTrace, markTrace, List.length_append, List.length_cons, List.length_nil,
    seek_length, separate_length, List.length_reverse]
  omega

theorem align_last (a bit : Bool) (left digits suffix : List Bool) :
    (alignTrace a bit left digits suffix).getLast? = some
      (state 134 (true :: bit :: true :: a :: left)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)) := by
  simp [alignTrace, List.getLast?_append, separate_last]

theorem align_chain (a bit : Bool) (left digits suffix : List Bool) :
    (alignTrace a bit left digits suffix).IsChain (fun before after =>
      Turing.TM0.step alignMachine before = some after) := by
  have htail := append_link (seekTrace bit a left [] digits suffix)
    (separateTrace bit a left digits.reverse suffix) _ _ (seek_chain bit a left [] digits suffix)
    (separate_chain bit a left digits.reverse suffix)
    (seek_last bit a left [] digits suffix) (separate_head bit a left digits.reverse suffix)
    (by
      cases bit <;> simp [Turing.TM0.step, alignMachine, state, checkB, hole,
        frontierLeft, Turing.Tape.mk₂])
  have hhead : (seekTrace bit a left [] digits suffix ++ separateTrace bit a left digits.reverse suffix).head? = some
      (state 3 (false :: a :: left)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix)) := by
    simp [List.head?_append, seek_head, frontierLeft, PSTRTMRawNat010.leftBlocks]
  apply append_link _ _ _ _ (mark_chain a bit left digits suffix) htail (by rfl) hhead
  simp [Turing.TM0.step, alignMachine, state, Turing.Tape.mk₂]

/-- The real step consumed by the binary-add alignment loop: one ACTUAL A
digit and B digit become a four-cell column on the left, all remaining A
digits and EVERY arbitrary suffix bit stay on the exact displayed tape. -/
theorem align_runsFrom (a bit : Bool) (left digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom alignMachine
      (state 0 left (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix)))
      (alignTrace a bit left digits suffix)
      (state 134 (true :: bit :: true :: a :: left)
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)) :=
  ⟨align_head a bit left digits suffix, align_chain a bit left digits suffix,
    align_last a bit left digits suffix, align_halt _ _⟩

theorem align_runs (a bit : Bool) (digits suffix : List Bool) :
    Runs alignMachine
      (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix))
      (alignTrace a bit [] digits suffix)
      (state 134 [true, bit, true, a]
        (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: suffix)) := by
  apply runs_of_chain
  · rfl
  · exact align_chain a bit [] digits suffix
  · exact align_last a bit [] digits suffix
  · exact align_halt _ _

theorem align_visitedSpace (a bit : Bool) (digits suffix : List Bool) :
    visitedSpace alignMachine
      (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix)).length
      (alignTrace a bit [] digits suffix) ≤ 26 * digits.length + suffix.length + 83 := by
  have hs := visitedSpace_le alignMachine
    (a :: true :: (PSTRTMIncrement009.blocks digits ++ false :: false :: true :: false :: bit :: true :: suffix)).length
    (alignTrace a bit [] digits suffix)
  rw [align_length] at hs
  simp only [List.length_cons, List.length_append, PSTRTMIncrement009.blocks_length] at hs ⊢
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMAlignUnit032
