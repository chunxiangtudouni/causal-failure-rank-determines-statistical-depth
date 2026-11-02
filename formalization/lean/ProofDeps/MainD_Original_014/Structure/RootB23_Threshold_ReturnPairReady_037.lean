module
public import Structure.RootB23_Threshold_ReturnReady_032
public import Structure.RootB23_Threshold_OutputArithmetic_Pair_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnPairReady
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

def bodyCode (capped : Bool) : Machine 3354 := PSTRTMSeq005.seqMachine (ReturnReady.bodyCode capped) OutputArithmetic.Pair.code
def rows (phase : Fin 2) : Machine 3354 := bodyCode (phase.val==1)
def ports (_phase : Fin 2) (_localLabel : Fin 3355) : Option (Fin 2 × Fin 3355) := none
def code : Machine 6709 := blockMachine rows ports
def entryFalse : Fin 6710 := label (p:=1) (s:=3354) 0 0
def entryTrue : Fin 6710 := label (p:=1) (s:=3354) 1 0
def exitFalse : Fin 6710 := label (p:=1) (s:=3354) 0 3354
def exitTrue : Fin 6710 := label (p:=1) (s:=3354) 1 3354
def entry (capped : Bool) : Fin 6710 := if capped then entryTrue else entryFalse
def exitPort (capped : Bool) : Fin 6710 := if capped then exitTrue else exitFalse
def liftCfg (phase : Fin 2) (state : MachineState 3354) : MachineState 6709 :=
  ⟨label (p:=1) (s:=3354) phase state.q,state.Tape⟩
def finalTape (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : Tape Bool :=
  Tape.mk₂ (List.replicate 9 false++ReturnReady.archive risk depth y left) (BTarget.fields risk depth)
def fee (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : ℕ :=
  ReturnReady.fee risk depth y left+8192*(natBits (PaperProofs.Statistics.controllerB risk depth)+1)^2

theorem output_exact (risk : Rat) (depth : ℕ) :
    OutputArithmetic.Pair.output (PaperProofs.Statistics.controllerB risk depth)=BTarget.fields risk depth := by
  simp [OutputArithmetic.Pair.output,OutputArithmetic.Target.value,OutputArithmetic.Target.denominator,
    BTarget.fields,PaperProofs.Statistics.controllerTarget,add_comm]

theorem body_bounded (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<ReturnFarActual.product risk depth y) :
    BoundedRun (bodyCode (ReturnFarActual.branch risk depth y))
      (ReturnActual.finalTape risk depth y left right) 3354 (finalTape risk depth y left) (fee risk depth y left) := by
  have first:=ReturnReady.body_bounded risk depth y left right positive
  have pair:=OutputArithmetic.Pair.bounded (List.replicate 8 false++ReturnReady.archive risk depth y left)
    (PaperProofs.Statistics.controllerB risk depth)
  rw [output_exact] at pair
  have actual:=first.seq pair
  have port : PSTRTMSeq005.rightLabel (a:=2620) (733 : Fin 734)=(3354 : Fin 3355) := by decide
  rw [port] at actual
  have prefixEq : false::(List.replicate 8 false++ReturnReady.archive risk depth y left)=
      List.replicate 9 false++ReturnReady.archive risk depth y left := rfl
  rw [prefixEq] at actual
  simpa only [bodyCode,finalTape] using actual.mono (b:=fee risk depth y left) (by rfl)

theorem actual_run (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<ReturnFarActual.product risk depth y) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨entry (ReturnFarActual.branch risk depth y),ReturnActual.finalTape risk depth y left right⟩ trace
      ⟨exitPort (ReturnFarActual.branch risk depth y),finalTape risk depth y left⟩ ∧ trace.length≤fee risk depth y left := by
  obtain ⟨part,run,time⟩:=body_bounded risk depth y left right positive
  cases found : ReturnFarActual.branch risk depth y with
  | false=>
    have atRow : PSTRTMSeq005.RunsFrom (rows (0 : Fin 2))
        ⟨0,ReturnActual.finalTape risk depth y left right⟩ part ⟨3354,finalTape risk depth y left⟩ := by
      simpa only [found,rows,show ((0 : Fin 2).val==1)=false by decide] using run
    have lifted:=block_runsFrom rows ports (0 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (0 : Fin 2)),?_,?_⟩
    · exact lifted
    · rw [List.length_map]
      exact time
  | true=>
    have atRow : PSTRTMSeq005.RunsFrom (rows (1 : Fin 2))
        ⟨0,ReturnActual.finalTape risk depth y left right⟩ part ⟨3354,finalTape risk depth y left⟩ := by
      simpa only [found,rows,show ((1 : Fin 2).val==1)=true by decide] using run
    have lifted:=block_runsFrom rows ports (1 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (1 : Fin 2)),?_,?_⟩
    · exact lifted
    · rw [List.length_map]
      exact time

theorem actual_contract (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<ReturnFarActual.product risk depth y) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨entry (ReturnFarActual.branch risk depth y),ReturnActual.finalTape risk depth y left right⟩ trace
      ⟨exitPort (ReturnFarActual.branch risk depth y),finalTape risk depth y left⟩ ∧
      trace.length≤fee risk depth y left ∧
      ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock)≤chargedLength+2*fee risk depth y left+1 := by
  obtain ⟨trace,run,time⟩:=actual_run risk depth y left right positive
  refine ⟨trace,run,time,?_⟩
  intro chargedLength clock
  have space:=PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.ReturnPairReady
