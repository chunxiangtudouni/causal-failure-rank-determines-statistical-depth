module
public import Common.PSTR_TM_ThresholdCountdownResolve_165

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownRun166
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdCountdownCode164 PSTRTMThresholdCountdownResolve165

def carryPrefix (archive : List Bool) (count : Nat) (later suffix : List Bool) : List (MachineState 8) :=
  [state 0 (processedLeft archive count) (false::true::remaining later suffix),
    state 2 (processedLeft archive count) (true::true::remaining later suffix),
    state 3 (true::processedLeft archive count) (true::remaining later suffix)]

theorem carryPrefix_chain (archive : List Bool) (count : Nat) (later suffix : List Bool) :
    (carryPrefix archive count later suffix).IsChain
      (fun before after => Turing.TM0.step countdownMachine before=some after) := by
  simp [carryPrefix,List.isChain_cons_cons,state,Turing.TM0.step,countdownMachine,Turing.Tape.mk₂]

/-- Ghost recursion describes the single real nine-label countdown
program. The count records real overwritten low zeros, not an input or
a fuel/answer certificate. Positive input ensures the borrow resolves
within the original word, so EVERY right suffix cell remains untouched. -/
def borrowTrace (archive : List Bool) (count : Nat) : List Bool → List Bool → List (MachineState 8)
  | [],_ => []
  | false::later,suffix => carryPrefix archive count later suffix++borrowTrace archive (count+1) later suffix
  | true::later,suffix => resolveTrace archive count later suffix

theorem borrow_head (archive : List Bool) (count : Nat) (digits suffix : List Bool) (hp : true∈digits) :
    (borrowTrace archive count digits suffix).head?=some
      (state 0 (processedLeft archive count) (PSTRTMIncrement009.blocks digits++suffix)) := by
  cases digits with
  | nil => simp at hp
  | cons bit later =>
    cases bit with
    | false => rfl
    | true => exact resolve_head _ _ _ _

theorem borrow_last (archive : List Bool) (count : Nat) (digits suffix : List Bool) (hp : true∈digits) :
    (borrowTrace archive count digits suffix).getLast?=some
      (state 8 (false::archive)
        (PSTRTMIncrement009.blocks (List.replicate count true++predDigits digits)++suffix)) := by
  induction digits generalizing count with
  | nil => simp at hp
  | cons bit later ih =>
    cases bit with
    | false =>
      have ht : true∈later := by simpa only [List.mem_cons,Bool.true_eq_false,false_or] using hp
      have h := ih (count+1) ht
      simp only [borrowTrace,List.getLast?_append,h,Option.some_or]
      simp only [predDigits,List.replicate_succ',List.append_assoc,List.singleton_append]
    | true => exact resolve_last _ _ _ _

theorem borrow_chain (archive : List Bool) (count : Nat) (digits suffix : List Bool) (hp : true∈digits) :
    (borrowTrace archive count digits suffix).IsChain
      (fun before after => Turing.TM0.step countdownMachine before=some after) := by
  induction digits generalizing count with
  | nil => simp at hp
  | cons bit later ih =>
    cases bit with
    | false =>
      have ht : true∈later := by simpa only [List.mem_cons,Bool.true_eq_false,false_or] using hp
      apply List.IsChain.append (carryPrefix_chain _ _ _ _) (ih (count+1) ht)
      intro before hb after ha
      simp only [carryPrefix,List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      rw [borrow_head archive (count+1) later suffix ht] at ha
      have he := Option.mem_some_iff.mp ha
      subst before
      subst after
      simp [Turing.TM0.step,countdownMachine,state,processedLeft,remaining,List.replicate_succ,
        PSTRTMRawNat010.leftBlocks,Turing.Tape.mk₂]
    | true => exact resolve_chain _ _ _ _

theorem borrow_length_le (archive : List Bool) (count : Nat) (digits suffix : List Bool) (hp : true∈digits) :
    (borrowTrace archive count digits suffix).length≤2*count+5*digits.length+3 := by
  induction digits generalizing count with
  | nil => simp at hp
  | cons bit later ih =>
    cases bit with
    | false =>
      have ht : true∈later := by simpa only [List.mem_cons,Bool.true_eq_false,false_or] using hp
      have h := ih (count+1) ht
      simp only [borrowTrace,List.length_append,carryPrefix,List.length_cons,List.length_nil] at h ⊢
      omega
    | true =>
      simp only [borrowTrace,resolve_length,List.length_cons]
      omega

theorem countdown_runsFrom (archive digits suffix : List Bool) (hp : true∈digits) :
    PSTRTMSeq005.RunsFrom countdownMachine
      (state 0 (false::archive) (PSTRTMIncrement009.blocks digits++suffix))
      (borrowTrace archive 0 digits suffix)
      (state 8 (false::archive) (PSTRTMIncrement009.blocks (predDigits digits)++suffix)) := by
  refine ⟨?_,borrow_chain _ _ _ _ hp,?_,?_⟩
  · simpa only [processedLeft,List.replicate_zero,PSTRTMRawNat010.leftBlocks,List.flatMap_nil,List.nil_append] using
      borrow_head archive 0 digits suffix hp
  · simpa only [List.replicate_zero,List.nil_append] using borrow_last archive 0 digits suffix hp
  · simp [Turing.TM0.step,countdownMachine,state]

theorem countdown_visitedSpace_le (archive digits suffix : List Bool) (hp : true∈digits) :
    visitedSpace countdownMachine (archive.length+1+2*digits.length+suffix.length)
      (borrowTrace archive 0 digits suffix)≤archive.length+suffix.length+12*digits.length+8 := by
  have ht := borrow_length_le archive 0 digits suffix hp
  have hs := PSTRTMTrace002.visitedSpace_le countdownMachine (archive.length+1+2*digits.length+suffix.length)
    (borrowTrace archive 0 digits suffix)
  omega

theorem natural_countdown_runsFrom (archive suffix : List Bool) (value : Nat) (hp : 0 < value) :
    PSTRTMSeq005.RunsFrom countdownMachine
      (state 0 (false::archive) (PSTRTMIncrement009.blocks (PSTRTMNatValue017.rawPayload value)++suffix))
      (borrowTrace archive 0 (PSTRTMNatValue017.rawPayload value) suffix)
      (state 8 (false::archive)
        (PSTRTMIncrement009.blocks (predDigits (PSTRTMNatValue017.rawPayload value))++suffix)) := by
  apply countdown_runsFrom
  apply has_true_of_value_pos
  simpa only [PSTRTMNatValue017.valueDigits_rawPayload] using hp

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCountdownRun166
