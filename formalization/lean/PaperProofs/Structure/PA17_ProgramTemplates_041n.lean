module
public import PaperProofs.Structure.PA17_ProgramTemplates_041m
public import PaperProofs.Structure.PA17_QueryTemplates_044g

/-! Static compiler certificates for both actual complete builder templates.
The recursive Decidable certificates are checked by kernel reduction. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
open PA17UniformGenerator035d PA17QueryTemplates044g
attribute [local instance] scopedDec belowDec stackDec inputsDec avoidsDec

theorem full_parentScoped : wrappedFull.codeTemplate.WellScoped (insert 3 {1, 2}) := by decide
theorem full_below : wrappedFull.codeTemplate.Below 64 := by decide
theorem full_stackFits : wrappedFull.codeTemplate.StackFits 64 1024 := by decide
theorem full_inputsBelow : wrappedFull.codeTemplate.InputsBelow 3 := by decide
theorem full_countersAvoid : PA17UniformGenerator035e.CountersAvoid 0 wrappedFull.codeTemplate := by decide

theorem rolling_parentScoped : wrappedRolling.codeTemplate.WellScoped (insert 3 {1, 2}) := by decide
theorem rolling_below : wrappedRolling.codeTemplate.Below 64 := by decide
theorem rolling_stackFits : wrappedRolling.codeTemplate.StackFits 64 1024 := by decide
theorem rolling_inputsBelow : wrappedRolling.codeTemplate.InputsBelow 3 := by decide
theorem rolling_countersAvoid : PA17UniformGenerator035e.CountersAvoid 0 wrappedRolling.codeTemplate := by decide

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
