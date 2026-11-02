module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanNumeric
public import Structure.PA06_A19Prepare_StaticMetadata036_StageIteration
public import Structure.PA06_A19Prepare_CompactWord008
public import PaperProofs.Structure.RawCandidateWorkspaceInit

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED numeric facts for the actual17-op raw stage read and
14-op streaming comparison. The old workspace polynomial is used only as
an already-proved logarithmic word-value bound, never as an allocation.
The actual memory allocation remains the original same8192 factory. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (mass highCacheEnd loadRel storeRel)

theorem rawStageBit_le_one (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin full.length) (tool : Fin q) :
    rawStageBit (rawIncidenceROM q full) stage.val tool.val ≤ 1 := by
  rw [rawStageBit, raw_header_q, raw_bit q full stage tool]
  simp only [bit]
  split_ifs <;> omega

/-- This is a width bound for the genuine raw input address only. It
neither adds workspace to the actual heap nor requests a caller estimate. -/
theorem actual_stage_input_end_le_wordLimit (q : Nat) (full : List (Finset (Fin q))) :
    2 + full.length * q ≤ metadataWordLimit (indexWidth 32 full.length q) := by
  apply metadata_le_wordLimit
  apply PA06A19PrepareCompactWord008.fits_width32_of_width16
  apply lt_of_le_of_lt _ (RawCandidateWorkspaceInit.workspaceBase_fits full.length q)
  unfold RawCandidateWorkspaceInit.workspaceBase RawCandidateWorkspaceInit.candidateCount
  nlinarith

theorem stageRead_numeric (q : Nat) (full : List (Finset (Fin q))) (B H CB : Nat)
    (stage : Fin full.length) (tool : Fin q) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hs : state.heap (CB + 22) = stage.val) (ht : state.heap (CB + 20) = tool.val)
    (hq : state.heap (CB + 1) = q)
    (hinput : 2 + full.length * q ≤ B)
    (hroom : highCacheEnd CB (mass q full) < H) (hH : H ≤ B) :
    NumericSafe B H (rawIncidenceROM q full) stageRead state := by
  have hstage := stage.isLt
  have htool := tool.isLt
  have hproduct : stage.val * q + tool.val < full.length * q := by
    calc
      stage.val * q + tool.val < stage.val * q + q := Nat.add_lt_add_left htool _
      _ = (stage.val + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ full.length * q := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hstage)
  have hbit : (rawIncidenceROM q full).semantic.read .input (2 + stage.val * q + tool.val) ≤ 1 := by
    rw [raw_bit q full stage tool]
    simp only [bit]
    split_ifs <;> omega
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 17 at hc
    interval_cases count <;> cases reg <;>
      simp_all [stageRead, loadRel, storeRel, runOps, natExecuteOp, natArithmetic,
        Op.execute, Instruction.execute, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    all_goals unfold highCacheEnd at hroom; omega
  · intro count hc
    change count < 17 at hc
    interval_cases count <;>
      simp_all [stageRead, loadRel, storeRel, runOps, natExecuteOp, natArithmetic,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits,
        rawIncidenceROM, PhysicalROM.words, PhysicalROM.semantic, incidence_length,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    all_goals unfold highCacheEnd at hroom; omega

theorem stageCompare_numeric (rom : PhysicalROM) (B H CB M : Nat) (state : NatState)
    (hr : RegistersLE B state) (hCB : state.register .address = CB)
    (hmatch : state.heap (CB + 23) ≤ 1) (hstage : state.heap (CB + 24) ≤ 1)
    (hvalue : state.register .value ≤ 1)
    (hroom : highCacheEnd CB M < H) (hH : H ≤ B) :
    NumericSafe B H rom stageCompare state := by
  constructor
  · intro count hc reg
    have hreg := hr reg
    change count ≤ 14 at hc
    interval_cases count <;> cases reg <;>
      simp_all [stageCompare, loadRel, storeRel, runOps, natExecuteOp,
        Op.execute, Instruction.execute]
    all_goals unfold highCacheEnd at hroom
    all_goals first | omega | (split_ifs <;> omega)
  · intro count hc
    change count < 14 at hc
    interval_cases count <;>
      simp_all [stageCompare, loadRel, storeRel, runOps, natExecuteOp,
        Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals unfold highCacheEnd at hroom; omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
