module
public import Common.PSTR_TM_ThresholdTrimBack_206
public import Common.PSTR_TM_TrimRun_111

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdTrimFrame207
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMTrimCode103 PSTRTMThresholdTrimBack206

theorem enter_advance (archive reversed : List Bool) :
    Turing.TM0.step trimMachine (state 2 (PSTRTMRawNat010.leftBlocks reversed ++ false::archive) []) =
      some (PSTRTMThresholdTrimBack206.initial archive reversed) := by
  cases reversed <;> simp [PSTRTMThresholdTrimBack206.initial,PSTRTMRawNat010.leftBlocks,
    Turing.TM0.step,trimMachine,state,Turing.Tape.mk₂]

def trimTrace (archive digits : List Bool) : List (MachineState 16) :=
  PSTRTMTrimRun111.scanTrace (false::archive) digits ++
    (state 2 (PSTRTMRawNat010.leftBlocks digits.reverse ++ false::archive) [] :: backTrace archive digits.reverse)

def trimFinal (archive digits : List Bool) : MachineState 16 :=
  state 14 (false::archive) (PSTRTMIncrement009.blocks (trimmed digits))

/-- Same frozen17-label trimmer, now with a true retained threshold
archive. Positive input guarantees its high-zero erasure reaches a ONE
before the original false guard. Every erased flag and rewind is real. -/
theorem trim_runsFrom (archive digits : List Bool) (hp : true ∈ digits) :
    PSTRTMSeq005.RunsFrom trimMachine (state 0 (false::archive) (PSTRTMIncrement009.blocks digits))
      (trimTrace archive digits) (trimFinal archive digits) := by
  have hr : true ∈ digits.reverse := by simpa only [List.mem_reverse] using hp
  refine ⟨?_,?_,?_,trim_halt _ _⟩
  · simp only [trimTrace,List.head?_append,PSTRTMTrimRun111.scan_head,Option.some_or]
  · apply (PSTRTMTrimRun111.scan_chain (false::archive) digits).append
    · apply List.isChain_cons.mpr
      constructor
      · intro after ha
        rw [back_head archive digits.reverse hr] at ha
        have he := Option.mem_some_iff.mp ha
        subst after
        exact enter_advance _ _
      · exact back_chain archive digits.reverse hr
    · intro before hb after ha
      rw [PSTRTMTrimRun111.scan_last] at hb
      simp only [List.head?_cons,Option.mem_some_iff] at ha
      have he := Option.mem_some_iff.mp hb
      subst before
      subst after
      exact PSTRTMTrimRun111.scan_advance _
  · have hn : backTrace archive digits.reverse ≠ [] := by
      intro he
      have hh := back_head archive digits.reverse hr
      simp [he] at hh
    simp only [trimTrace,List.getLast?_append,List.getLast?_cons_of_ne_nil hn,
      back_last archive digits.reverse hr,Option.some_or,trimFinal]
    rfl

theorem trim_final_tape (archive digits : List Bool) :
    (trimFinal archive digits).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload (PSTRTMIncrement009.valueDigits digits))) := by
  change Turing.Tape.mk₂ _ (PSTRTMIncrement009.blocks (trimmed digits)) = _
  rw [PSTRTMTrimValue104.trimmed_canonical]

theorem trim_length_le (archive digits : List Bool) :
    (trimTrace archive digits).length ≤ 16*(digits.length + 1) := by
  have hb := back_length_le archive digits.reverse
  rw [List.length_reverse] at hb
  simp only [trimTrace,List.length_append,List.length_cons,PSTRTMTrimRun111.scan_length]
  omega

theorem trim_visitedSpace_le (archive digits : List Bool) (inputLength : Nat) :
    visitedSpace trimMachine inputLength (trimTrace archive digits) ≤ inputLength + 32*(digits.length + 1) + 1 := by
  have ht := trim_length_le archive digits
  have hs := PSTRTMTrace002.visitedSpace_le trimMachine inputLength (trimTrace archive digits)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdTrimFrame207
