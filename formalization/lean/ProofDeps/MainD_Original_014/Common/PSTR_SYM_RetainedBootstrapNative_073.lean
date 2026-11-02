module

public import Common.PSTR_SYM_RetainedBootstrapRun_072
public import Common.PSTR_SYM_OriginalBootstrap_058

/-! SAME retained-LEFT bootstrap in the frozen finite native machine.
The exact entry is control0 with the real nonempty left archive, not a
new initial/reset instruction. All source steps and terminal HALT map
lockstep; prefix space below is a relative component measurement. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRetainedBootstrap

open Turing PSTRTMSeq005 PSTRSymbolicRelabel PSTRSymbolicRawBootstrap

/-- The frozen053 cursor-specific transport, generalized only to another
fixed finite code table and actual physical entry. No input trace is
provided by an original caller in the consuming theorem below. -/
theorem finite_from_univ {Λ : Type*} [Inhabited Λ] [Fintype Λ]
    (machine : TM0.Machine Bool Λ) (entry final : TM0.Cfg Bool Λ) (trace : List (TM0.Cfg Bool Λ))
    (first : trace.head? = some entry)
    (chain : trace.IsChain (fun before after => TM0.step machine before = some after))
    (last : trace.getLast? = some final) (halt : TM0.step machine final = none) :
    RunsFrom (finiteMachine machine (Finset.univ : Finset Λ))
      (relabelCfg (finiteLabels (Finset.univ : Finset Λ)) entry)
      (trace.map (relabelCfg (finiteLabels (Finset.univ : Finset Λ))))
      (relabelCfg (finiteLabels (Finset.univ : Finset Λ)) final) := by
  have each (state : TM0.Cfg Bool Λ) :
      (TM0.step machine state).map (relabelCfg (finiteLabels (Finset.univ : Finset Λ))) =
        TM0.step (finiteMachine machine (Finset.univ : Finset Λ))
          (relabelCfg (finiteLabels (Finset.univ : Finset Λ)) state) :=
    relabel_step machine ((Finset.univ : Finset Λ) : Set Λ)
      (finiteLabels (Finset.univ : Finset Λ)) (finiteDecode (Finset.univ : Finset Λ))
      (by intro q _; exact finite_inverse _ q (Finset.mem_univ q)) state (Finset.mem_univ state.q)
  refine ⟨?_,?_,?_,?_⟩
  · simp only [List.head?_map,first,Option.map_some]
  · apply (List.isChain_map _).mpr
    apply chain.imp
    intro before after edge
    have step := each before
    rw [edge] at step
    exact step.symm
  · simp only [List.getLast?_map,last,Option.map_some]
  · have step := each final
    rw [halt] at step
    exact step.symm

def bootstrapCost (count first second : Nat) : Nat :=
  32 * (natBits count + 1)^2 + 18 * natBits count + 32 +
    128 * ((encodeDatum (.natural first)).length + 1)^2 +
    128 * ((encodeDatum (.natural second)).length + 1)^2

theorem actual_native_bootstrap_from_guard (count first second : Nat) (archive suffix : List Bool)
    (room : 2 ≤ count) :
    ∃ (trace : List (MachineState bootSupport.card)) (final : MachineState bootSupport.card),
      RunsFrom bootstrapMachine
        ⟨0,Tape.mk₂ (false :: archive) (bootstrapInput count first second suffix)⟩ trace final ∧
      final.q = (finiteLabels bootSupport) BootLabel.halt ∧
      final.Tape = bootstrapTapeFrom archive count first second suffix ∧
      trace.length ≤ bootstrapCost count first second ∧
      ∀ inputLength clock, visitedSpace bootstrapMachine inputLength (trace.take clock) ≤
        inputLength + 2 * bootstrapCost count first second + 1 := by
  obtain ⟨oldTrace,oldFinal,firstHead,chain,lastHead,port,tape,halt,time⟩ :=
    actual_bootstrap_from_guard count first second archive suffix room
  let trace := oldTrace.map (relabelCfg (finiteLabels bootSupport))
  let final := relabelCfg (finiteLabels bootSupport) oldFinal
  have actual := finite_from_univ bootstrapCode
    ⟨.entry 0,Tape.mk₂ (false :: archive) (bootstrapInput count first second suffix)⟩
    oldFinal oldTrace firstHead chain lastHead halt
  have initialLabel : (finiteLabels bootSupport) (BootLabel.entry 0) = 0 :=
    (finiteLabels bootSupport).map_pt
  have initial : relabelCfg (finiteLabels bootSupport)
      (⟨.entry 0,Tape.mk₂ (false :: archive) (bootstrapInput count first second suffix)⟩ : TM0.Cfg Bool BootLabel) =
      (⟨0,Tape.mk₂ (false :: archive) (bootstrapInput count first second suffix)⟩ : MachineState bootSupport.card) := by
    simp only [relabelCfg,initialLabel]
  change RunsFrom bootstrapMachine (relabelCfg (finiteLabels bootSupport) _)
    (oldTrace.map (relabelCfg (finiteLabels bootSupport))) (relabelCfg (finiteLabels bootSupport) oldFinal) at actual
  rw [initial] at actual
  have length : trace.length = oldTrace.length := List.length_map _
  change oldTrace.length ≤ bootstrapCost count first second at time
  refine ⟨trace,final,actual,?_,tape,?_,?_⟩
  · change (finiteLabels bootSupport) oldFinal.q = (finiteLabels bootSupport) BootLabel.halt
    rw [port]
  · rw [length]
    exact time
  · intro inputLength clock
    have cells := PSTRTMTrace002.visitedSpace_le bootstrapMachine inputLength (trace.take clock)
    have takeLength : (trace.take clock).length ≤ oldTrace.length := by
      simp only [List.length_take,length]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicRetainedBootstrap
