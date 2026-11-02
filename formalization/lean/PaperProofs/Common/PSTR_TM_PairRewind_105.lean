module
public import PaperProofs.Common.PSTR_TM_MulRewind_085
public import PaperProofs.Common.PSTR_TM_RawNat_010

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPairRewind105
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMMulRewind085

theorem rewind_halt (left right : List Bool) : Turing.TM0.step rewindMachine (state 3 left right)=none := by
  simp [Turing.TM0.step,rewindMachine,state]

/-- The already fixed085 rewind is used on arbitrary actual flagged digit
lists by C projection and high-zero trimming, rather than assuming their
length is a multiple of the earlier multiplication tuple arity. -/
def initial (archive : List Bool) : List Bool → List Bool → MachineState 3
  | [],tail => state 1 archive (false::tail)
  | bit::earlier,tail => state 1 (bit::(PSTRTMRawNat010.leftBlocks earlier++false::archive)) (true::tail)
def loopTrace (archive : List Bool) : List Bool → List Bool → List (MachineState 3)
  | [],tail => [initial archive [] tail,state 3 (false::archive) tail]
  | bit::earlier,tail => initial archive (bit::earlier) tail ::
      state 2 (PSTRTMRawNat010.leftBlocks earlier++false::archive) (bit::true::tail) ::
      loopTrace archive earlier (bit::true::tail)

theorem loop_head (archive earlier tail : List Bool) :
    (loopTrace archive earlier tail).head?=some (initial archive earlier tail) := by
  cases earlier <;> rfl
theorem loop_last (archive earlier tail : List Bool) :
    (loopTrace archive earlier tail).getLast?=some (state 3 (false::archive) (PSTRTMIncrement009.blocks earlier.reverse++tail)) := by
  induction earlier generalizing tail with
  | nil => rfl
  | cons bit earlier ih =>
    have hne : loopTrace archive earlier (bit::true::tail)≠[] := by
      intro h
      have hh := loop_head archive earlier (bit::true::tail)
      simp [h] at hh
    simp only [loopTrace,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMIncrement009.blocks,List.reverse_cons,List.flatMap_append,List.append_assoc]
theorem loop_length (archive earlier tail : List Bool) :
    (loopTrace archive earlier tail).length=2*earlier.length+2 := by
  induction earlier generalizing tail with
  | nil => rfl
  | cons bit earlier ih => simp only [loopTrace,List.length_cons,ih]; omega

theorem loop_chain (archive earlier tail : List Bool) :
    (loopTrace archive earlier tail).IsChain (fun x y => Turing.TM0.step rewindMachine x=some y) := by
  induction earlier generalizing tail with
  | nil => simp [loopTrace,initial,List.isChain_cons_cons,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
  | cons bit earlier ih =>
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [initial,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [loop_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases earlier <;> simp [initial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
    · exact ih _

def fullTrace (archive earlier tail : List Bool) : List (MachineState 3) :=
  state 0 (PSTRTMRawNat010.leftBlocks earlier++false::archive) tail ::loopTrace archive earlier tail

theorem full_head (archive earlier tail : List Bool) :
    (fullTrace archive earlier tail).head?=some (state 0 (PSTRTMRawNat010.leftBlocks earlier++false::archive) tail) := rfl
theorem full_last (archive earlier tail : List Bool) :
    (fullTrace archive earlier tail).getLast?=some (state 3 (false::archive) (PSTRTMIncrement009.blocks earlier.reverse++tail)) := by
  have hne : loopTrace archive earlier tail≠[] := by
    intro h
    have hh := loop_head archive earlier tail
    simp [h] at hh
  rw [fullTrace,List.getLast?_cons_of_ne_nil hne,loop_last]
theorem full_length (archive earlier tail : List Bool) :
    (fullTrace archive earlier tail).length=2*earlier.length+3 := by
  simp only [fullTrace,List.length_cons,loop_length]
theorem full_chain (archive earlier tail : List Bool) :
    (fullTrace archive earlier tail).IsChain (fun x y => Turing.TM0.step rewindMachine x=some y) := by
  apply List.isChain_cons.mpr
  constructor
  · intro after ha
    rw [loop_head] at ha
    have he := Option.mem_some_iff.mp ha
    subst after
    cases earlier <;> simp [initial,PSTRTMRawNat010.leftBlocks,Turing.TM0.step,rewindMachine,state,Turing.Tape.mk₂]
  · exact loop_chain archive earlier tail

/-- Actual EOF to first digit, preserving EVERY arbitrary archive cell
past the actually read false guard and every retained tail cell. Exact
2*N+3 trace configurations, no arity/cursor-reset/length input assumption. -/
theorem rewind_runsFrom (archive digits tail : List Bool) :
    PSTRTMSeq005.RunsFrom rewindMachine (state 0 (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) tail)
      (fullTrace archive digits.reverse tail) (state 3 (false::archive) (PSTRTMIncrement009.blocks digits++tail)) := by
  refine ⟨full_head _ _ _,full_chain _ _ _,?_,rewind_halt _ _⟩
  simpa only [List.reverse_reverse] using full_last archive digits.reverse tail

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPairRewind105
