module
public import Common.PSTR_TM_ThresholdUnitColumnsCost_160

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBFooter187
open PaperProofs.Common.Native.RationalControllerComputation

/-- Actual threshold B-to-backup call adapter. Scan the live flags and
write the second genuine blank end cell TRUE. This is exactly the
nearest-field footer convention used by the existing Copy006, without
implementing or assuming a copy/allocator. Actual blank RIGHT required. -/
def footerMachine : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 0 else 2,if symbol then .move .right else .write true)
  | _ => none

def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def fieldLeft (archive previous : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks previous++false::archive

def footerTrace (archive previous : List Bool) : List Bool → List (MachineState 2)
  | [] => [state 0 (fieldLeft archive previous) [],
      state 1 (false::fieldLeft archive previous) [],state 2 (false::fieldLeft archive previous) [true]]
  | bit::later => state 0 (fieldLeft archive previous) (PSTRTMIncrement009.blocks (bit::later))::
      state 1 (bit::fieldLeft archive previous) (true::PSTRTMIncrement009.blocks later)::
      footerTrace archive (bit::previous) later

theorem footer_head (archive previous digits : List Bool) :
    (footerTrace archive previous digits).head?=some
      (state 0 (fieldLeft archive previous) (PSTRTMIncrement009.blocks digits)) := by cases digits <;> rfl

theorem footer_last (archive previous digits : List Bool) :
    (footerTrace archive previous digits).getLast?=some
      (state 2 (false::fieldLeft archive (digits.reverse++previous)) [true]) := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih =>
    have hn : footerTrace archive (bit::previous) later≠[] := by
      intro h
      have hh := footer_head archive (bit::previous) later
      simp only [h,List.head?_nil,reduceCtorEq] at hh
    rw [footerTrace,List.getLast?_cons_cons,List.getLast?_cons_of_ne_nil hn,ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem footer_chain (archive previous digits : List Bool) :
    (footerTrace archive previous digits).IsChain
      (fun before after => Turing.TM0.step footerMachine before=some after) := by
  induction digits generalizing previous with
  | nil => simp [footerTrace,List.isChain_cons_cons,Turing.TM0.step,footerMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    rw [footerTrace]
    apply List.isChain_cons_cons.mpr
    constructor
    · simp [Turing.TM0.step,footerMachine,state,Turing.Tape.mk₂,PSTRTMIncrement009.blocks]
    apply List.isChain_cons.mpr
    constructor
    · intro after ha
      rw [footer_head] at ha
      have he := Option.mem_some_iff.mp ha
      subst after
      cases later <;> simp [Turing.TM0.step,footerMachine,state,fieldLeft,
        PSTRTMRawNat010.leftBlocks,Turing.Tape.mk₂,PSTRTMIncrement009.blocks]
    · exact ih _

theorem footer_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom footerMachine (state 0 (false::archive) (PSTRTMIncrement009.blocks digits))
      (footerTrace archive [] digits)
      (state 2 (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) [true]) := by
  refine ⟨?_,footer_chain _ _ _,?_,?_⟩
  · simpa only [fieldLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_nil,List.nil_append] using footer_head archive [] digits
  · simpa only [fieldLeft,List.append_nil] using footer_last archive [] digits
  · simp [Turing.TM0.step,footerMachine,state]

theorem footer_length (archive previous digits : List Bool) :
    (footerTrace archive previous digits).length=2*digits.length+3 := by
  induction digits generalizing previous with
  | nil => rfl
  | cons bit later ih => simp only [footerTrace,List.length_cons,ih]; omega

theorem footer_visitedSpace_le (archive digits : List Bool) :
    visitedSpace footerMachine (archive.length+1+2*digits.length) (footerTrace archive [] digits)≤
      archive.length+6*digits.length+8 := by
  have h := PSTRTMTrace002.visitedSpace_le footerMachine (archive.length+1+2*digits.length) (footerTrace archive [] digits)
  rw [footer_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdBFooter187
