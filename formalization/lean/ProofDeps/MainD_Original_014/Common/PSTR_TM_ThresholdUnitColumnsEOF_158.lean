module
public import Common.PSTR_TM_ThresholdUnitColumnsStep_157

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsEOF158
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdUnitColumnsCode156 PSTRTMThresholdUnitColumnsStep157 PSTRTMOverlap132

def rewindLabel (q : Fin 4) : Fin 214 := ⟨210+q.val,by have hq := q.isLt; omega⟩

attribute [local implicit_reducible] Turing.TM0.Machine rewindLabel

theorem rewind_command (q : Fin 4) (symbol : Bool) :
    unitMachine (rewindLabel q) symbol=
      (PSTRTMMulRewind085.rewindMachine q symbol).map
        (fun (next,statement) => (rewindLabel next,statement)) := by
  have hq := q.isLt
  have h0 : ¬210+q.val<2 := by omega
  have h1 : ¬210+q.val<6 := by omega
  have h2 : ¬210+q.val<10 := by omega
  have h3 : ¬210+q.val<14 := by omega
  have h4 : ¬210+q.val<178 := by omega
  have h5 : ¬210+q.val<210 := by omega
  conv_lhs =>
    unfold unitMachine
    dsimp only [rewindLabel]
  rw [dite_eq_right h0,dite_eq_right h1,dite_eq_right h2,dite_eq_right h3,dite_eq_right h4,dite_eq_right h5]
  simp only [Nat.add_sub_cancel_left,Fin.eta,rewindLabel]

theorem rewind_step (configuration : MachineState 3) :
    Turing.TM0.step unitMachine (liftRewind configuration)=
      (Turing.TM0.step PSTRTMMulRewind085.rewindMachine configuration).map liftRewind := by
  cases configuration with
  | mk q tape =>
    change Turing.TM0.step unitMachine ⟨rewindLabel q,tape⟩=_
    simp only [Turing.TM0.step,rewind_command]
    cases h : PSTRTMMulRewind085.rewindMachine q tape.head with
    | none => simp
    | some value =>
      obtain ⟨next,statement⟩ := value
      cases statement <;> simp [liftRewind,rewindLabel]

theorem liftRewind_halt (left right : List Bool) :
    liftRewind (PSTRTMMulRewind085.state 3 left right)=state 213 left right := by
  have hq : (⟨210+(3 : Fin 4).val,by decide⟩ : Fin 214)=(213 : Fin 214) := by decide
  exact congrArg (fun label : Fin 214 => (⟨label,Turing.Tape.mk₂ left right⟩ : MachineState 213)) hq

def leftOf (archive previous : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks previous++false::archive

def eofPrefix (archive previous : List Bool) (first : Bool) : List (MachineState 213) :=
  [state (startLabel first) (leftOf archive previous) [],
    state (readLabel first false) (false::leftOf archive previous) [],
    liftRewind (PSTRTMMulRewind085.state 0 (leftOf archive previous) [])]

theorem eofPrefix_chain (archive previous : List Bool) (first : Bool) :
    (eofPrefix archive previous first).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) := by
  cases first <;> simp [eofPrefix,List.isChain_cons_cons,state,startLabel,readLabel,saved,liftRewind,
    PSTRTMMulRewind085.state,Turing.TM0.step,unitMachine,Turing.Tape.mk₂,PSTRTMRawNat010.blank_single_false]

def rewindTrace (archive previous : List Bool) : List (MachineState 213) :=
  (PSTRTMPairRewind105.fullTrace archive previous []).map liftRewind

theorem rewind_head (archive previous : List Bool) :
    (rewindTrace archive previous).head?=some
      (liftRewind (PSTRTMMulRewind085.state 0 (leftOf archive previous) [])) := by
  simpa only [rewindTrace,List.head?_map,Option.map_some,leftOf] using
    congrArg (Option.map liftRewind) (PSTRTMPairRewind105.full_head archive previous [])

theorem rewind_last (archive previous : List Bool) :
    (rewindTrace archive previous).getLast?=some
      (state 213 (false::archive) (PSTRTMIncrement009.blocks previous.reverse)) := by
  simpa only [rewindTrace,List.getLast?_map,Option.map_some,List.append_nil,liftRewind_halt] using
    congrArg (Option.map liftRewind) (PSTRTMPairRewind105.full_last archive previous [])

theorem rewind_chain (archive previous : List Bool) :
    (rewindTrace archive previous).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply (PSTRTMPairRewind105.full_chain archive previous []).imp
  intro before after h
  simp only [rewind_step,h,Option.map_some]

def eofTrace (archive previous : List Bool) (first : Bool) : List (MachineState 213) :=
  glue (eofPrefix archive previous first) (rewindTrace archive previous)

theorem eof_head (archive previous : List Bool) (first : Bool) :
    (eofTrace archive previous first).head?=some (state (startLabel first) (leftOf archive previous) []) :=
  glue_head _ _ _ _ rfl rfl (rewind_head _ _)

theorem eof_last (archive previous : List Bool) (first : Bool) :
    (eofTrace archive previous first).getLast?=some
      (state 213 (false::archive) (PSTRTMIncrement009.blocks previous.reverse)) :=
  glue_last _ _ _ (rewind_last _ _)

theorem eof_chain (archive previous : List Bool) (first : Bool) :
    (eofTrace archive previous first).IsChain
      (fun before after => Turing.TM0.step unitMachine before=some after) :=
  glue_chain unitMachine _ _ _ (eofPrefix_chain _ _ _) (rewind_chain _ _) rfl (rewind_head _ _)

theorem eof_length (archive previous : List Bool) (first : Bool) :
    (eofTrace archive previous first).length=2*previous.length+5 := by
  simp only [eofTrace,glue_length,eofPrefix,rewindTrace,List.length_map,
    List.length_cons,List.length_nil,PSTRTMPairRewind105.full_length]
  omega

theorem unit_halt (left right : List Bool) : Turing.TM0.step unitMachine (state 213 left right)=none := by
  have h := rewind_step (PSTRTMMulRewind085.state 3 left right)
  rw [liftRewind_halt,PSTRTMPairRewind105.rewind_halt] at h
  exact h

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitColumnsEOF158

