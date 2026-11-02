module
public import Common.PSTR_TM_ThresholdCountdownCode_164

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownResolve165
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCountdownCode164

def processedLeft (archive : List Bool) (count : Nat) : List Bool :=
  PSTRTMRawNat010.leftBlocks (List.replicate count true)++false::archive

def remaining (later suffix : List Bool) : List Bool := PSTRTMIncrement009.blocks later++suffix

def resolvePrefix (archive : List Bool) (count : Nat) (later suffix : List Bool) : List (MachineState 8) :=
  [state 0 (processedLeft archive count) (true::true::remaining later suffix),
    state 1 (processedLeft archive count) (false::true::remaining later suffix),
    state 4 (false::processedLeft archive count) (true::remaining later suffix)]

theorem resolvePrefix_chain (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (resolvePrefix archive count later suffix).IsChain
      (fun before after => Turing.TM0.step countdownMachine before=some after) := by
  simp [resolvePrefix,List.isChain_cons_cons,state,Turing.TM0.step,countdownMachine,Turing.Tape.mk₂]

def rewindTrace (archive : List Bool) (count : Nat) (later suffix : List Bool) : List (MachineState 8) :=
  (PSTRTMPairRewind105.fullTrace archive (false::List.replicate count true) (remaining later suffix)).map liftRewind

private theorem liftRewind_start (left right : List Bool) :
    liftRewind (PSTRTMMulRewind085.state 0 left right)=state 5 left right := by
  have hq : (⟨5+(0 : Fin 4).val,by decide⟩ : Fin 9)=(5 : Fin 9) := by decide
  exact congrArg (fun label : Fin 9 => (⟨label,Turing.Tape.mk₂ left right⟩ : MachineState 8)) hq

theorem rewind_head (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (rewindTrace archive count later suffix).head?=some
      (state 5 (true::false::processedLeft archive count) (remaining later suffix)) := by
  simpa only [rewindTrace,List.head?_map,Option.map_some,liftRewind_start,state,
    processedLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_cons,List.cons_append,List.nil_append] using
    congrArg (Option.map liftRewind)
      (PSTRTMPairRewind105.full_head archive (false::List.replicate count true) (remaining later suffix))

theorem rewind_last (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (rewindTrace archive count later suffix).getLast?=some
      (state 8 (false::archive)
        (PSTRTMIncrement009.blocks (List.replicate count true++false::later)++suffix)) := by
  simpa [rewindTrace,List.getLast?_map,liftRewind,PSTRTMMulRewind085.state,state,
    remaining,PSTRTMIncrement009.blocks,List.reverse_cons,List.reverse_replicate,
    List.flatMap_append,List.append_assoc] using
    congrArg (Option.map liftRewind)
      (PSTRTMPairRewind105.full_last archive (false::List.replicate count true) (remaining later suffix))

theorem rewind_chain (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (rewindTrace archive count later suffix).IsChain
      (fun before after => Turing.TM0.step countdownMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply (PSTRTMPairRewind105.full_chain archive (false::List.replicate count true) (remaining later suffix)).imp
  intro before after h
  simp only [PSTRTMThresholdCountdownCode164.rewind_step,h,Option.map_some]

def resolveTrace (archive : List Bool) (count : Nat) (later suffix : List Bool) : List (MachineState 8) :=
  resolvePrefix archive count later suffix++rewindTrace archive count later suffix

theorem resolve_head (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (resolveTrace archive count later suffix).head?=some
      (state 0 (processedLeft archive count) (true::true::remaining later suffix)) := rfl

theorem resolve_last (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (resolveTrace archive count later suffix).getLast?=some
      (state 8 (false::archive)
        (PSTRTMIncrement009.blocks (List.replicate count true++false::later)++suffix)) := by
  simp only [resolveTrace,List.getLast?_append,rewind_last,Option.some_or]

theorem resolve_chain (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (resolveTrace archive count later suffix).IsChain
      (fun before after => Turing.TM0.step countdownMachine before=some after) := by
  apply List.IsChain.append (resolvePrefix_chain _ _ _ _) (rewind_chain _ _ _ _)
  intro before hb after ha
  simp only [resolvePrefix,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
  rw [rewind_head] at ha
  have he := Option.mem_some_iff.mp ha
  subst before
  subst after
  simp [Turing.TM0.step,countdownMachine,state,Turing.Tape.mk₂]

theorem resolve_length (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (resolveTrace archive count later suffix).length=2*count+8 := by
  simp only [resolveTrace,resolvePrefix,rewindTrace,List.length_append,List.length_map,
    List.length_cons,List.length_nil,PSTRTMPairRewind105.full_length,List.length_replicate]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownResolve165
