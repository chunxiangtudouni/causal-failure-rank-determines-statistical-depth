module
public import Paid.PDCompute_CoreSearch_Budget_Search_003
public import Paid.PDCompute_SolverCoreScale_218

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreSearchBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDLower.CoreSearch

theorem coreOperandBound_positive (P : Parameters) (fee : ℚ) : 1≤coreOperandBound P fee:=by
  unfold coreOperandBound
  omega

/-- Uniform price size has NO table/tools/entry-count factor. The
original core envelope already pays every grid through J+1. -/
theorem original_priceBudget_le_core (P : Parameters) (fee : ℚ) :
    priceBudget P (P.bisectionBudget fee)≤16*coreOperandBound P fee:=by
  let J:=P.bisectionBudget fee
  let L:=ratEncodingBits P.Lambda
  let R:=ratEncodingBits P.certificate.risk
  have gridWeight : J+L+1≤(J+1)*(L+R+1):=by nlinarith [Nat.zero_le (J*L),Nat.zero_le (J*R)]
  have weight : (J+1)*(L+R+1)≤coreOperandBound P fee:=by
    unfold coreOperandBound
    dsimp only [J,L,R]
    omega
  have positive:=coreOperandBound_positive P fee
  unfold priceBudget
  dsimp only [J,L,R] at gridWeight
  dsimp only [J,L,R] at weight
  omega

theorem original_stats_le_core (P : Parameters) (fee : ℚ) :
    solverStatsBits P fee P.certificate.stages≤1280*coreOperandBound P fee:=by
  have stats:=solverStatsBits_le_scale P fee 0 P.certificate.stages P.tools
  have source:=solverBitScale_core_additive P fee 0
  have zero : ratEncodingBits (0:ℚ)=3:=by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  rw [zero] at source
  have combined:=stats.trans (Nat.mul_le_mul_left 256 source)
  have positive:=coreOperandBound_positive P fee
  omega

theorem originalScalarScale_le_core (P : Parameters) (fee : ℚ) :
    originalScalarScale P fee≤2048*coreOperandBound P fee:=by
  have price:=original_priceBudget_le_core P fee
  have stats:=original_stats_le_core P fee
  have positive:=coreOperandBound_positive P fee
  have risk : ratEncodingBits P.certificate.risk≤coreOperandBound P fee:=by unfold coreOperandBound rawSize;omega
  have feeBits : ratEncodingBits fee≤coreOperandBound P fee:=by unfold coreOperandBound rawSize;omega
  unfold originalScalarScale uniformScalarScale
  omega

/-- Exact room required by the actual017 arithmetic scripts, chosen
ONCE from the original input envelope and reused across every round. -/
theorem original_scalar_room_le_core (P : Parameters) (fee : ℚ) :
    1+scalarValueBudget (originalScalarScale P fee)≤524288*coreOperandBound P fee:=by
  have source:=originalScalarScale_le_core P fee
  have positive:=coreOperandBound_positive P fee
  unfold scalarValueBudget
  omega

end PDCompute.CoreSearchBudget
