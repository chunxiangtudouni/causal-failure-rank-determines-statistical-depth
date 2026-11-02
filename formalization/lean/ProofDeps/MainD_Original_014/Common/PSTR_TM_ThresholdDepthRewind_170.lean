module
public import Common.PSTR_TM_PairRewind_105

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthRewind170
open PaperProofs.Common.Native.RationalControllerComputation

/-- Existing105 flag rewind, with its actual FLAG-reading label as the
entry. This three-label code does not perform a free head reset: it is
entered where163 physically stopped, at the last depth flag. -/
def rewindMachine : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => some (if symbol then 1 else 2,if symbol then .move .left else .move .right)
  | 1 => some (0,.move .left)
  | _ => none

def state (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def lowerCfg (configuration : MachineState 3) : MachineState 2 :=
  ⟨⟨configuration.q.val-1,by have hq := configuration.q.isLt; omega⟩,configuration.Tape⟩

private theorem lowerCfg_halt (left right : List Bool) :
    lowerCfg (PSTRTMMulRewind085.state 3 left right)=state 2 left right := by
  have hq : (⟨(3 : Fin 4).val-1,by decide⟩ : Fin 3)=(2 : Fin 3) := by decide
  exact congrArg (fun label : Fin 3 => (⟨label,Turing.Tape.mk₂ left right⟩ : MachineState 2)) hq

theorem lower_step (configuration : MachineState 3) (hq : 1≤configuration.q.val) :
    Turing.TM0.step rewindMachine (lowerCfg configuration)=
      (Turing.TM0.step PSTRTMMulRewind085.rewindMachine configuration).map lowerCfg := by
  cases configuration with
  | mk q tape =>
    fin_cases q <;> cases hs : tape.head <;>
      simp_all [lowerCfg,Turing.TM0.step,rewindMachine,PSTRTMMulRewind085.rewindMachine]

theorem old_loop_labels (archive previous tail : List Bool) :
    ∀ configuration∈PSTRTMPairRewind105.loopTrace archive previous tail,1≤configuration.q.val := by
  induction previous generalizing tail with
  | nil =>
    intro configuration hm
    simp only [PSTRTMPairRewind105.loopTrace,List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl
    · change 1≤(1 : Fin 4).val
      decide
    · change 1≤(3 : Fin 4).val
      decide
  | cons bit earlier ih =>
    intro configuration hm
    simp only [PSTRTMPairRewind105.loopTrace,List.mem_cons] at hm
    rcases hm with rfl|rfl|hm
    · change 1≤(1 : Fin 4).val
      decide
    · change 1≤(2 : Fin 4).val
      decide
    · exact ih _ _ hm

def initial (archive digits tail : List Bool) : MachineState 2 :=
  lowerCfg (PSTRTMPairRewind105.initial archive digits.reverse tail)

def rewindTrace (archive digits tail : List Bool) : List (MachineState 2) :=
  (PSTRTMPairRewind105.loopTrace archive digits.reverse tail).map lowerCfg

theorem initial_label (archive digits tail : List Bool) : (initial archive digits tail).q=0 := by
  unfold initial
  cases digits.reverse <;> rfl

theorem rewind_chain (archive digits tail : List Bool) :
    (rewindTrace archive digits tail).IsChain
      (fun before after => Turing.TM0.step rewindMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply List.IsChain.imp_of_mem_imp (p:=PSTRTMPairRewind105.loop_chain archive digits.reverse tail)
  intro before after hb _ hstep
  rw [lower_step before (old_loop_labels _ _ _ before hb),hstep]
  rfl

theorem rewind_runsFrom (archive digits tail : List Bool) :
    PSTRTMSeq005.RunsFrom rewindMachine (initial archive digits tail) (rewindTrace archive digits tail)
      (state 2 (false::archive) (PSTRTMIncrement009.blocks digits++tail)) := by
  refine ⟨?_,rewind_chain _ _ _,?_,?_⟩
  · simpa only [rewindTrace,List.head?_map,initial,Option.map_some] using
      congrArg (Option.map lowerCfg) (PSTRTMPairRewind105.loop_head archive digits.reverse tail)
  · simpa only [rewindTrace,List.getLast?_map,lowerCfg_halt,
      Option.map_some,List.reverse_reverse] using
      congrArg (Option.map lowerCfg) (PSTRTMPairRewind105.loop_last archive digits.reverse tail)
  · simp [Turing.TM0.step,rewindMachine,state]

theorem rewind_length (archive digits tail : List Bool) :
    (rewindTrace archive digits tail).length=2*digits.length+2 := by
  simp only [rewindTrace,List.length_map,PSTRTMPairRewind105.loop_length,List.length_reverse]

theorem rewind_visitedSpace_le (archive digits tail : List Bool) :
    visitedSpace rewindMachine (archive.length+1+2*digits.length+tail.length) (rewindTrace archive digits tail)≤
      archive.length+tail.length+6*digits.length+6 := by
  have h := PSTRTMTrace002.visitedSpace_le rewindMachine (archive.length+1+2*digits.length+tail.length)
    (rewindTrace archive digits tail)
  rw [rewind_length] at h
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthRewind170
