module

public import Paid.PDROC_BitVM_VM_Phases_Execute_011
public import Paid.PDROC_BitVM_VM_Phases_SourceBudget_012
public import Paid.PDROC_BitVM_VM_Phases_OriginalEnvelope_013
public import Paid.PDROC_BitVM_VM_Phases_InputBounds_001
public import RootD27Core_CanonicalCapsule_Runs_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Original

open Turing PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open _root_.PDROC.BitVM.VM.Phases.Polynomial

/-- The capsule chooses the original actual prepare/core programs before
ALL inputs. The same two traces supply both outputs and the shared clock.
Only their public original types cross the normal module boundary. -/
theorem original_source (backend : ISA.RatBackend) :
    ∃ (prepareCode coreCode : Program) (C degree : ℕ), 0 < C ∧
      ∀ (P : Parameters) (fee : ℚ), 0 ≤ fee →
      ∃ (trace : List (Phases.State backend prepareCode coreCode)) (terminal : Phases.State backend prepareCode coreCode),
        trace.head? = some (TM2.init (0 : ISA.Stack) (encodeBits (rawInput P fee))) ∧
        trace.IsChain (fun a b => TM2.step (Phases.program backend prepareCode coreCode) a = some b) ∧
        trace.getLast? = some terminal ∧ TM2.step (Phases.program backend prepareCode coreCode) terminal = none ∧
        terminal.stk 0 = encodeBits (encodeArtifact (buildArtifact P fee)) ∧
        trace.length ≤ C * (variableGammaSize P fee)^degree := by
  obtain ⟨prepareCode,coreCode,numericC,numericD,_numericPositive,actualNumeric⟩ :=
    RootD27.Core.CanonicalCapsule.actual_prepare_core_uniform
  obtain ⟨prepareC,prepareD,coreC,coreD,_pc,_pd,_cc,_cd,execute⟩ :=
    Execute.execute_bounded backend prepareCode coreCode
  let E := OriginalEnvelope.envelope numericC numericD
  let prepBudget := fun S => SourceBudget.envelopeCost prepareC prepareD (E S)
  let coreBudget := fun S => SourceBudget.envelopeCost coreC coreD (E S)
  have eBound : ScalarBound E := OriginalEnvelope.scalar numericC numericD
  have prepBound : ScalarBound prepBudget := SourceBudget.envelopeCost_scalar eBound prepareC prepareD
  have coreBound : ScalarBound coreBudget := SourceBudget.envelopeCost_scalar eBound coreC coreD
  have inputBound : ScalarBound (fun S => 24*S) := (ScalarBound.constant 24).mul ScalarBound.identity
  obtain ⟨C,degree,positive,budgetBound⟩ := schedule8_scalar Resources.coefficient
    (Calls.globalPushCap backend prepareCode coreCode) inputBound prepBound coreBound
  refine ⟨prepareCode,coreCode,C,degree,positive,?_⟩
  intro P fee nonnegative
  obtain ⟨prepareStates,prepareFinal,coreStates,coreFinal,prepareRuns,prepareOutput,coreRuns,
      _decoded,coreOutput,prepareTime,_prepareSpace,prepareBits,coreTime,_coreSpace,coreBits⟩ :=
    actualNumeric P fee nonnegative
  let S := variableGammaSize P fee
  have positiveS : 1 ≤ S := Size.variable_positive P fee
  have rawLength : (encodeBits (rawInput P fee)).length ≤ 24*S := Size.raw_input_length P fee
  have preparedLength := InputBounds.prepared_from_runs prepareCode P fee prepareStates prepareFinal
    prepareRuns prepareOutput (peakOperandBits prepareStates) (le_refl _)
  obtain ⟨rawI,prepareT,prepareB,preparedI,coreT,coreB⟩ :=
    OriginalEnvelope.dominate_internal numericC numericD S (encodeBits (rawInput P fee)).length
      (time prepareCode prepareStates) (peakOperandBits prepareStates)
      (time coreCode coreStates) (peakOperandBits coreStates) (encodeBits (preparedInput P fee)).length
      positiveS rawLength prepareTime prepareBits coreTime coreBits preparedLength
  have prepareBound : CFG.Complete.totalBudget prepareC prepareD prepareCode (rawInput P fee) prepareStates + 1 ≤
      prepBudget S := SourceBudget.totalBudget_le prepareC prepareD (E S) prepareCode (rawInput P fee)
        prepareStates prepareT prepareB rawI
  have computedBound : CFG.Complete.totalBudget coreC coreD coreCode (preparedInput P fee) coreStates + 1 ≤
      coreBudget S := SourceBudget.totalBudget_le coreC coreD (E S) coreCode (preparedInput P fee)
        coreStates coreT coreB preparedI
  obtain ⟨terminal,path,halted,word,clock⟩ :=
    execute (rawInput P fee) (preparedInput P fee) (encodeArtifact (buildArtifact P fee))
      prepareStates prepareFinal coreStates coreFinal (prepBudget S) (coreBudget S)
      rfl prepareRuns prepareOutput (InputBounds.prepared_count P fee) coreRuns coreOutput prepareBound computedBound
  let trace := Phases.before backend prepareCode coreCode (rawContents (encodeBits (rawInput P fee))) :: path.posts
  refine ⟨trace,terminal,?_,path.chain,path.last,halted,word,?_⟩
  · exact congrArg some (before_eq_init backend prepareCode coreCode (encodeBits (rawInput P fee)))
  · change path.posts.length + 1 ≤ C*S^degree
    exact (clock.trans (schedule8_mono Resources.coefficient (Calls.globalPushCap backend prepareCode coreCode)
      rawLength (le_refl _) (le_refl _))).trans (budgetBound S positiveS)

end PDROC.BitVM.VM.Phases.Original
