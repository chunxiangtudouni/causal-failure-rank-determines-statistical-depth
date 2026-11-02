module
public import Paid.PDCompute_CoreGlobalBudget_Room_002
public import Paid.PDCompute_CoreMemory_Layout_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreGlobalBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits PDCompute.Solver PDCompute.CoreSearchBudget PDLower.CoreRuntimeNumeric

/-- The already frozen physical global region, including the REAL
calibration 6M+25 words; this is an address bound, not a sum over calls. -/
abbrev addressLimit (P : Parameters) : ℕ :=
  PDCompute.CoreMemory.globalSpan P.certificate.M P.certificate.stages P.tools

theorem addressLimit_runtime (P : Parameters) :
    addressLimit P=runtimeAddressLimit P+(6*P.certificate.M+25) := rfl

theorem addressLimit_bits (P : Parameters) (fee : ℚ) :
    (Cell.natural (addressLimit P)).bits≤64*coreOperandBound P fee := by
  have runtime:=runtime_address_room_le_core P fee
  have mul:=natBits_mul_le 6 P.certificate.M
  have add:=natBits_add_le (6*P.certificate.M) 25
  have sum:=natBits_add_le (runtimeAddressLimit P) (6*P.certificate.M+25)
  have constants : natBits 6=3 ∧ natBits 25=5 := by decide
  have terms : natBits P.certificate.M≤coreOperandBound P fee := by unfold coreOperandBound;omega
  have positive:=coreOperandBound_positive P fee
  change 1+natBits (runtimeAddressLimit P)≤32*coreOperandBound P fee at runtime
  change 1+natBits (addressLimit P)≤_
  rw [addressLimit_runtime]
  omega

theorem budget_natural (P : Parameters) (fee : ℚ) (pcUpper value : ℕ)
    (inside : value≤addressLimit P) : (Cell.natural value).bits≤budget P fee pcUpper := by
  have bits:=natBits_mono inside
  have address:=addressLimit_bits P fee
  have room:=budget_core P fee pcUpper
  change 1+natBits value≤_
  change 1+natBits (addressLimit P)≤64*coreOperandBound P fee at address
  omega

theorem runtime_le_addressLimit (P : Parameters) : runtimeAddressLimit P≤addressLimit P := by
  rw [addressLimit_runtime]
  omega

theorem budget_runtime_natural (P : Parameters) (fee : ℚ) (pcUpper value : ℕ)
    (inside : value≤runtimeAddressLimit P) : (Cell.natural value).bits≤budget P fee pcUpper :=
  budget_natural P fee pcUpper value (inside.trans (runtime_le_addressLimit P))

theorem budget_header (P : Parameters) (fee : ℚ) (pcUpper value : ℕ) (inside : value≤48) :
    (Cell.natural value).bits≤budget P fee pcUpper := by
  apply budget_runtime_natural P fee pcUpper value
  unfold runtimeAddressLimit
  omega

theorem budget_base (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    (Cell.natural (99+2*P.certificate.M)).bits≤budget P fee pcUpper :=
  budget_runtime_natural P fee pcUpper _ (runtime_base_le_limit P)

theorem budget_workspace_cap (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    (Cell.natural (PDCompute.Pack.naturalCap (99+2*P.certificate.M)
      P.certificate.stages P.tools)).bits≤budget P fee pcUpper := by
  apply budget_runtime_natural P fee pcUpper
  have size:=workspaceSize_linear P.certificate.stages P.tools
  unfold PDCompute.Pack.naturalCap runtimeAddressLimit
  omega

theorem budget_source_end (P : Parameters) (fee penalty : ℚ) (pcUpper : ℕ) :
    (Cell.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools+
      (RootD27.Core.originalSolveEncoding P fee penalty).length)).bits≤budget P fee pcUpper :=
  budget_runtime_natural P fee pcUpper _ (runtime_source_end_le_limit P fee penalty)

theorem budget_retained_end (P : Parameters) (fee penalty : ℚ) (pcUpper : ℕ) (upper : Bool) :
    (Cell.natural (RootD27.Core.retainedTableBase (99+2*P.certificate.M)
      P.certificate.stages P.tools upper+(RootD27.Core.originalSolveEncoding P fee penalty).length)).bits≤budget P fee pcUpper :=
  budget_runtime_natural P fee pcUpper _ (runtime_target_end_le_limit P fee penalty upper)

theorem budget_endpoint_cursor (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    1+natBits (96+(1+2*(P.certificate.M+1)))≤budget P fee pcUpper := by
  have base:=budget_base P fee pcUpper
  change 1+natBits (99+2*P.certificate.M)≤_ at base
  have equality : 96+(1+2*(P.certificate.M+1))=99+2*P.certificate.M := by omega
  rw [equality]
  exact base

theorem budget_endpoint_count (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    1+natBits (P.certificate.M+1)≤budget P fee pcUpper := by
  have count:=solver_core_endpointCount_bits P fee
  have room:=budget_core P fee pcUpper
  omega

theorem budget_counter (P : Parameters) (fee : ℚ) (pcUpper value : ℕ)
    (inside : value≤P.bisectionBudget fee) : (Cell.natural value).bits≤budget P fee pcUpper := by
  have valueBits:=(natBits_mono inside).trans (natBits_le_succ (P.bisectionBudget fee))
  have weight:=Nat.mul_le_mul_left (P.bisectionBudget fee+1)
    (by omega : 1≤ratEncodingBits P.Lambda+ratEncodingBits P.certificate.risk+1)
  simp only [Nat.mul_one] at weight
  have core : (P.bisectionBudget fee+1)*(ratEncodingBits P.Lambda+ratEncodingBits P.certificate.risk+1)≤
      coreOperandBound P fee := by unfold coreOperandBound;omega
  have room:=budget_core P fee pcUpper
  change 1+natBits value≤_
  omega

end PDCompute.CoreGlobalBudget
