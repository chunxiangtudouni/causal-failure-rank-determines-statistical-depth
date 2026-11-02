module
public import Structure.PA17_TM_RatArithmetic_FirstRaw_052a

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstRaw052
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticMulStart049 PA17TMRatArithmeticParse002
attribute [local implicit_reducible] stageCap mulStartCap commonCap bridgeCap

/-- This is the actual original-input prefix segment of the fixed bridge
code. Its next step is a real write-self into the consumer, not a relabel.
The consumer's initial configuration pays for that step when concatenated. -/
theorem original_prefix_segment {states : Nat} (k : Nat) (consumer : Machine states)
    (entry : Fin 64→Fin (states+1)) (x y : Rat) :
    ∃ trace, Segment (bridgeMachine k consumer entry)
      (TM0.init (encode [.rational x,.rational y])) trace (prefixFinal k states x y) ∧
      TM0.step (bridgeMachine k consumer entry) (prefixFinal k states x y)=
        some (consumerState k states (entry (actualMemory x y)) (originalFinal k x y).Tape) ∧
      trace.length≤(16*k+533)*(fieldWidth x y+1)^4 := by
  obtain ⟨trace,hr,hl⟩ := original_mulStart_runs k x y
  have localRun : PSTRTMSeq005.RunsFrom (mulStartMachine k)
      (TM0.init (encode [.rational x,.rational y])) trace (originalFinal k x y) :=
    ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩
  have hp := pad_runsFrom (prefix_le_common k states) (mulStartMachine k) _ _ _ localRun
  have hf : PSTRTMSeq005.RunsFrom (bridgeFamily k consumer (0 : Fin 2))
      (padCfg (prefix_le_common k states)
        (TM0.init (encode [.rational x,.rational y]) : MachineState (mulStartCap k)))
      (trace.map (padCfg (prefix_le_common k states)))
      (padCfg (prefix_le_common k states) (originalFinal k x y)) := by
    simpa only [bridgeFamily,Fin.val_zero,ite_true] using hp
  have hs := block_segment (bridgeFamily k consumer) (bridgePorts k states entry) (0 : Fin 2) _ _ _ hf
  have initial : blockCfg (0 : Fin 2)
      (padCfg (prefix_le_common k states)
        (TM0.init (encode [.rational x,.rational y]) : MachineState (mulStartCap k)))=
      (TM0.init (encode [.rational x,.rational y]) : MachineState (bridgeCap k states)) := by
    change blockCfg (0 : Fin 2)
      (padCfg (prefix_le_common k states)
        (⟨0,Tape.mk₁ (encode [.rational x,.rational y])⟩ : MachineState (mulStartCap k)))=
      (⟨0,Tape.mk₁ (encode [.rational x,.rational y])⟩ : MachineState (bridgeCap k states))
    rw [pad_zero,blockCfg_zero]
  let fullTrace : List (MachineState (bridgeCap k states)) :=
    (trace.map (padCfg (prefix_le_common k states))).map (blockCfg (s:=commonCap k states) (0 : Fin 2))
  refine ⟨fullTrace,⟨hs.1.trans (congrArg some initial),hs.2.1,hs.2.2⟩,
    actual_transfer k consumer entry x y localRun.2.2.2,?_⟩
  simpa only [fullTrace,List.length_map] using hl

/-- An independently exhibited segment includes the actual target
configuration, so the real control transfer is explicitly charged +1. -/
theorem original_dispatch_segment {states : Nat} (k : Nat) (consumer : Machine states)
    (entry : Fin 64→Fin (states+1)) (x y : Rat) :
    ∃ trace, Segment (bridgeMachine k consumer entry)
      (TM0.init (encode [.rational x,.rational y])) trace
      (consumerState k states (entry (actualMemory x y)) (originalFinal k x y).Tape) ∧
      trace.length≤(16*k+533)*(fieldWidth x y+1)^4+1 := by
  obtain ⟨trace,hr,step,hl⟩ := original_prefix_segment k consumer entry x y
  let target := consumerState k states (entry (actualMemory x y)) (originalFinal k x y).Tape
  have singleton : Segment (bridgeMachine k consumer entry) target [target] target :=
    ⟨rfl,by simp,rfl⟩
  have hs := segment_append (bridgeMachine k consumer entry) _ _ _ _ trace [target] hr singleton step
  refine ⟨trace++[target],hs,?_⟩
  simp only [List.length_append,List.length_singleton]
  omega

theorem consumer_lift {states : Nat} (k : Nat) (consumer : Machine states)
    (entry : Fin 64→Fin (states+1)) (first last : MachineState states)
    (trace : List (MachineState states)) (run : PSTRTMSeq005.RunsFrom consumer first trace last) :
    PSTRTMSeq005.RunsFrom (bridgeMachine k consumer entry)
      (consumerState k states first.q first.Tape)
      ((trace.map (padCfg (consumer_le_common k states))).map (blockCfg (s:=commonCap k states) (1 : Fin 2)))
      (consumerState k states last.q last.Tape) := by
  have hp := pad_runsFrom (consumer_le_common k states) consumer first last trace run
  have hf : PSTRTMSeq005.RunsFrom (bridgeFamily k consumer (1 : Fin 2))
      (padCfg (consumer_le_common k states) first) (trace.map (padCfg (consumer_le_common k states)))
      (padCfg (consumer_le_common k states) last) := by
    simpa only [bridgeFamily,Fin.val_one,show ¬(1 : Nat)=0 from by decide,ite_false] using hp
  exact block_runsFrom (bridgeFamily k consumer) (bridgePorts k states entry) (1 : Fin 2) _ _ _ hf
    (by simp only [bridgePorts,Fin.val_one,show ¬(1 : Nat)=0 from by decide,ite_false])

/-- INTERNAL composition: an actual concrete consumer run must be
proved separately and instantiated before claiming the first multiplication.
Its trace begins at exactly the physical Tape/row reached by049. -/
theorem combine_actual {states : Nat} (k : Nat) (consumer : Machine states)
    (entry : Fin 64→Fin (states+1)) (x y : Rat) (last : MachineState states)
    (tailTrace : List (MachineState states))
    (run : PSTRTMSeq005.RunsFrom consumer
      ⟨entry (actualMemory x y),(originalFinal k x y).Tape⟩ tailTrace last) :
    ∃ trace, Runs (bridgeMachine k consumer entry) (encode [.rational x,.rational y]) trace
      (consumerState k states last.q last.Tape) ∧
      trace.length≤(16*k+533)*(fieldWidth x y+1)^4+tailTrace.length := by
  obtain ⟨prefixTrace,hprefix,step,hp⟩ := original_prefix_segment k consumer entry x y
  have hl := consumer_lift k consumer entry _ _ _ run
  let tailGlobal : List (MachineState (bridgeCap k states)) :=
    (tailTrace.map (padCfg (consumer_le_common k states))).map (blockCfg (s:=commonCap k states) (1 : Fin 2))
  have hs : Segment (bridgeMachine k consumer entry) _ tailGlobal _ := ⟨hl.1,hl.2.1,hl.2.2.1⟩
  have combined := segment_append (bridgeMachine k consumer entry) _ _ _ _ prefixTrace tailGlobal hprefix hs step
  refine ⟨prefixTrace++tailGlobal,
    PSTRTMTrace002.runs_of_chain _ _ _ _ combined.1 combined.2.1 combined.2.2 hl.2.2.2,?_⟩
  have length : tailGlobal.length=tailTrace.length := by simp only [tailGlobal,List.length_map]
  simp only [List.length_append,length]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstRaw052
