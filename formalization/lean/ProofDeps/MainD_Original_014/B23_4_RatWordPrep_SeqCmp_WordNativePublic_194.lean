module

public import B23_4_RatWordPrep_SeqCmp_WordOriginalResources_193

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Public

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation Resources

noncomputable def nativeCoefficient (C : Type*) : Nat :=
  1+wholeCoefficient C+16*wholeSpaceCoefficient C+wholeClockCoefficient C+
    wholeScanCoefficient C+wholeChargeCoefficient C+sourcePushCap C+sourceActionCap C

theorem nativeCoefficient_positive (C : Type*) : 0<nativeCoefficient C := by unfold nativeCoefficient; omega

theorem upgrade_degree (C : Type*) (coefficient bound : Nat) (small : coefficient≤nativeCoefficient C) :
    coefficient*(bound+1)^(wholeDegree C)≤nativeCoefficient C*(bound+1)^(2*wholeDegree C) :=
  Nat.mul_le_mul small (Nat.pow_le_pow_right (Nat.succ_pos bound) (by omega : wholeDegree C≤2*wholeDegree C))

structure NativeFacts {C : Type*} (source : Label → Statement C) (coefficient degree : Nat)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (trace : List (State C)) (final : State C) [Inhabited C] : Prop where
  first : trace.head?=some (TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store C) 0 (wordInput E target word))
  chain : trace.IsChain (fun before after => TM2.step source before=some after)
  last : trace.getLast?=some final
  halted : final.l=none
  stopped : TM2.step source final=none
  output : final.stk 0=wordOutput E target word
  time : trace.length≤coefficient*((wordInput E target word).length+1)^degree
  boundaries : ∀ current∈trace,
    RatInput.occupied current.stk≤coefficient*((wordInput E target word).length+1)^degree ∧
    ∀ slot,(current.stk slot).length≤coefficient*((wordInput E target word).length+1)^degree
  internal : ∀ current∈trace.dropLast,∀ point,current.l=some point→
    ∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
      RatInput.occupied node.2≤coefficient*((wordInput E target word).length+1)^degree ∧
      ∀ slot,(node.2 slot).length≤coefficient*((wordInput E target word).length+1)^degree
  clocks : ∀ current∈trace.dropLast,∀ point,current.l=some point→
    ScannerStatement.clock (source point) current.var current.stk≤coefficient*((wordInput E target word).length+1)^degree
  scan : traceClockSum source trace≤coefficient*((wordInput E target word).length+1)^degree
  charge : trace.length+traceClockSum source trace≤coefficient*((wordInput E target word).length+1)^degree
  counts : ∀ point,ScannerClock.actions (source point)≤coefficient ∧ AuxWorkspace.pushes (source point)≤coefficient

/-- Literal default init, full original wordOutput and true HALT, with
all native compiler input obligations discharged on the SAME trace.
The source and the uniform polynomial coefficient precede every input. -/
theorem actual_native_ready (C : Type*) [Inhabited C] (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ trace final,NativeFacts (program (C:=C) .halt) (nativeCoefficient C) (2*wholeDegree C) E target word trace final := by
  obtain ⟨final,run,halted,stopped,_context,output,_empty3,_empty13,_retained,bounds,scan,charge⟩ :=
    actual_original_resources C E target word
  let B := (wordInput E target word).length
  have timeCap : wholeCoefficient C≤nativeCoefficient C := by unfold nativeCoefficient; omega
  have spaceCap : wholeSpaceCoefficient C≤nativeCoefficient C := by unfold nativeCoefficient; omega
  have massCap : 16*wholeSpaceCoefficient C≤nativeCoefficient C := by unfold nativeCoefficient; omega
  have clockCap : wholeClockCoefficient C≤nativeCoefficient C := by unfold nativeCoefficient; omega
  have scanCap : wholeScanCoefficient C≤nativeCoefficient C := by unfold nativeCoefficient; omega
  have chargeCap : wholeChargeCoefficient C≤nativeCoefficient C := by unfold nativeCoefficient; omega
  have massBound : 16*(wholeSpaceCoefficient C*(B+1)^(wholeDegree C))≤nativeCoefficient C*(B+1)^(2*wholeDegree C) :=
    (Nat.le_of_eq (by ring : 16*(wholeSpaceCoefficient C*(B+1)^(wholeDegree C))=(16*wholeSpaceCoefficient C)*(B+1)^(wholeDegree C))).trans
      (upgrade_degree C _ B massCap)
  refine ⟨run.trace,final,⟨run.first.trans (congrArg some (initial_default _)),run.chain,run.last,
    halted,stopped,output,bounds.count.trans (upgrade_degree C _ B timeCap),?_,?_,?_,?_,?_,?_⟩⟩
  · intro current present
    refine ⟨(bounds.boundary_mass current present).trans massBound,?_⟩
    intro slot
    exact (bounds.boundary current present slot).trans (upgrade_degree C _ B spaceCap)
  · intro current present point selected node inside
    refine ⟨(bounds.internal_mass current present point selected node inside).trans massBound,?_⟩
    intro slot
    exact (bounds.internal current present point selected node inside slot).trans (upgrade_degree C _ B spaceCap)
  · intro current present point selected
    exact (bounds.clocks current present point selected).trans (upgrade_degree C _ B clockCap)
  · exact scan.trans (Nat.mul_le_mul_right _ scanCap)
  · exact charge.trans (Nat.mul_le_mul_right _ chargeCap)
  · intro point
    exact ⟨(source_actions (C:=C) point).trans (by unfold nativeCoefficient; omega),
      (source_pushes (C:=C) point).trans (by unfold nativeCoefficient; omega)⟩

theorem quantitative_fixed_source (C : Type*) [Fintype C] [Inhabited C] :
    ∃ source : Label → Statement C,∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧ Finite (Store C) ∧
      TM2.Supports source (Finset.univ : Finset Label) ∧
      ∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
        ∃ trace final,NativeFacts source coefficient degree E target word trace final :=
  ⟨program .halt,nativeCoefficient C,2*wholeDegree C,nativeCoefficient_positive C,
    Nat.mul_pos (by decide) (wholeDegree_positive C),FullStore.finite_store C,supports,actual_native_ready C⟩

/-- Closed consumer entry for the original WORD branch. -/
theorem original_word_native :
    ∃ source : Label → Statement Unit,∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧ Finite (Store Unit) ∧
      TM2.Supports source (Finset.univ : Finset Label) ∧
      ∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
        ∃ trace final,NativeFacts source coefficient degree E target word trace final :=
  quantitative_fixed_source Unit

end B23_4_RatWordPrep.WordFinish.Public
