module
public import Common.PSTR_TM_ThresholdDepthLoopCode_173

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopLift174
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthLoopCode173

attribute [local implicit_reducible] Turing.TM0.Machine prefixCfg zeroCfg positiveCfg nextCfg

def prefixPort (q : Fin 23) (tape : Turing.Tape Bool) : MachineState 387 :=
  ⟨if q.val=21 then 23 else 26,tape⟩

theorem zeroCfg_zero (tape : Turing.Tape Bool) :
    zeroCfg (⟨0,tape⟩ : MachineState 2)=(⟨23,tape⟩ : MachineState 387) := by
  have hq : (⟨23+(0 : Fin 3).val,by decide⟩ : Fin 388)=(23 : Fin 388) := by decide
  exact congrArg (fun label : Fin 388 => (⟨label,tape⟩ : MachineState 387)) hq

theorem positiveCfg_zero (tape : Turing.Tape Bool) :
    positiveCfg (⟨0,tape⟩ : MachineState 2)=(⟨26,tape⟩ : MachineState 387) := by
  have hq : (⟨26+(0 : Fin 3).val,by decide⟩ : Fin 388)=(26 : Fin 388) := by decide
  exact congrArg (fun label : Fin 388 => (⟨label,tape⟩ : MachineState 387)) hq

theorem prefix_step (configuration : MachineState 22) :
    Turing.TM0.step loopMachine (prefixCfg configuration)=
      match Turing.TM0.step PSTRTMThresholdCountdownPrefix172.prefixMachine configuration with
      | none => some (prefixPort configuration.q configuration.Tape)
      | some next => some (prefixCfg next) := by
  cases configuration with
  | mk q tape =>
    unfold Turing.TM0.step loopMachine prefixCfg
    simp only [dite_eq_left q.isLt,Fin.eta]
    cases h : PSTRTMThresholdCountdownPrefix172.prefixMachine q tape.head with
    | none => simp [prefixPort,Turing.Tape.write_self]
    | some value =>
      obtain ⟨next,statement⟩ := value
      cases statement <;> simp

theorem zero_step (configuration : MachineState 2) :
    Turing.TM0.step loopMachine (zeroCfg configuration)=
      match Turing.TM0.step PSTRTMThresholdCounterSeek169.seekMachine configuration with
      | none => some (final configuration.Tape)
      | some next => some (zeroCfg next) := by
  cases configuration with
  | mk q tape =>
    have hq := q.isLt
    have h0 : ¬23+q.val<23 := by omega
    have h1 : 23+q.val<26 := by omega
    unfold Turing.TM0.step loopMachine zeroCfg
    simp only [dite_eq_right h0,dite_eq_left h1,Nat.add_sub_cancel_left,Fin.eta]
    cases h : PSTRTMThresholdCounterSeek169.seekMachine q tape.head with
    | none => simp [final,Turing.Tape.write_self]
    | some value =>
      obtain ⟨next,statement⟩ := value
      cases statement <;> simp

theorem positive_step (configuration : MachineState 2) :
    Turing.TM0.step loopMachine (positiveCfg configuration)=
      match Turing.TM0.step PSTRTMThresholdCounterSeek169.seekMachine configuration with
      | none => some (nextCfg ⟨0,configuration.Tape⟩)
      | some next => some (positiveCfg next) := by
  cases configuration with
  | mk q tape =>
    have hq := q.isLt
    have h0 : ¬26+q.val<23 := by omega
    have h1 : ¬26+q.val<26 := by omega
    have h2 : 26+q.val<29 := by omega
    unfold Turing.TM0.step loopMachine positiveCfg
    simp only [dite_eq_right h0,dite_eq_right h1,dite_eq_left h2,Nat.add_sub_cancel_left,Fin.eta]
    cases h : PSTRTMThresholdCounterSeek169.seekMachine q tape.head with
    | none => simp [nextCfg,Turing.Tape.write_self]
    | some value =>
      obtain ⟨next,statement⟩ := value
      cases statement <;> simp

theorem next_step (configuration : MachineState 357) :
    Turing.TM0.step loopMachine (nextCfg configuration)=
      match Turing.TM0.step PSTRTMThresholdNextFrame162.nextMachine configuration with
      | none => some (prefixCfg ⟨0,configuration.Tape⟩)
      | some next => some (nextCfg next) := by
  cases configuration with
  | mk q tape =>
    have hq := q.isLt
    have h0 : ¬29+q.val<23 := by omega
    have h1 : ¬29+q.val<26 := by omega
    have h2 : ¬29+q.val<29 := by omega
    have h3 : 29+q.val<387 := by omega
    unfold Turing.TM0.step loopMachine nextCfg
    simp only [dite_eq_right h0,dite_eq_right h1,dite_eq_right h2,dite_eq_left h3,Nat.add_sub_cancel_left,Fin.eta]
    cases h : PSTRTMThresholdNextFrame162.nextMachine q tape.head with
    | none => simp [prefixCfg,Turing.Tape.write_self]
    | some value =>
      obtain ⟨next,statement⟩ := value
      cases statement <;> simp

theorem prefix_chain (trace : List (MachineState 22))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMThresholdCountdownPrefix172.prefixMachine before=some after)) :
    (trace.map prefixCfg).IsChain (fun before after => Turing.TM0.step loopMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply h.imp
  intro before after hs
  simp only [prefix_step,hs]

theorem zero_chain (trace : List (MachineState 2))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMThresholdCounterSeek169.seekMachine before=some after)) :
    (trace.map zeroCfg).IsChain (fun before after => Turing.TM0.step loopMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply h.imp
  intro before after hs
  simp only [zero_step,hs]

theorem positive_chain (trace : List (MachineState 2))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMThresholdCounterSeek169.seekMachine before=some after)) :
    (trace.map positiveCfg).IsChain (fun before after => Turing.TM0.step loopMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply h.imp
  intro before after hs
  simp only [positive_step,hs]

theorem next_chain (trace : List (MachineState 357))
    (h : trace.IsChain (fun before after => Turing.TM0.step PSTRTMThresholdNextFrame162.nextMachine before=some after)) :
    (trace.map nextCfg).IsChain (fun before after => Turing.TM0.step loopMachine before=some after) := by
  apply (List.isChain_map _).mpr
  apply h.imp
  intro before after hs
  simp only [next_step,hs]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthLoopLift174

