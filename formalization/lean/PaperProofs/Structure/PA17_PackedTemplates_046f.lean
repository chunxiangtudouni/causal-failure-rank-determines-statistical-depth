module
public import PaperProofs.Structure.PA17_PackedTemplates_046e

/-! Static checked properties of the same three actual physical templates.
Widths/bits and the measured-length snapshot use only reserved cells1/2/3. -/
@[expose] public section
set_option maxRecDepth 30000
set_option maxHeartbeats 6000000
namespace PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
open PA17UniformGenerator035d PA17QueryTemplates044g
attribute [local instance] scopedDec belowDec stackDec inputsDec avoidsDec

theorem full_scoped : full.WellScoped {1, 2} := by decide
theorem full_parentScoped : full.WellScoped (insert 3 {1, 2}) := by decide
theorem full_below : full.Below 64 := by decide
theorem full_stackFits : full.StackFits 64 1024 := by decide
theorem full_inputsBelow : full.InputsBelow 3 := by decide
theorem full_countersAvoid : PA17UniformGenerator035e.CountersAvoid 0 full := by decide

theorem query_scoped : query.WellScoped {1, 2} := by decide
theorem query_parentScoped : query.WellScoped (insert 3 {1, 2}) := by decide
theorem query_below : query.Below 64 := by decide
theorem query_stackFits : query.StackFits 64 1024 := by decide
theorem query_inputsBelow : query.InputsBelow 3 := by decide
theorem query_countersAvoid : PA17UniformGenerator035e.CountersAvoid 0 query := by decide

theorem rolling_scoped : rolling.WellScoped {1, 2} := by decide
theorem rolling_parentScoped : rolling.WellScoped (insert 3 {1, 2}) := by decide
theorem rolling_below : rolling.Below 64 := by decide
theorem rolling_stackFits : rolling.StackFits 64 1024 := by decide
theorem rolling_inputsBelow : rolling.InputsBelow 3 := by decide
theorem rolling_countersAvoid : PA17UniformGenerator035e.CountersAvoid 0 rolling := by decide

end PaperProofs.Structure.LaminarTree.PA17PackedTemplates046
