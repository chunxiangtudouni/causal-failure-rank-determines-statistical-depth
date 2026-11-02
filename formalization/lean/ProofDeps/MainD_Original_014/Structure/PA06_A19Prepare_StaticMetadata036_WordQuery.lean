module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordBounds
public import Structure.PA06_A19Prepare_ChildrenCache023_WordChunks

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Reuse frozen022's complete common32 query safety, rather than recoding
its branching paths. Arbitrary full-width caller registers are accepted.
This is one actual query component, not a full metadata Word completion. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023 (preparedSize mass actualControlBase actualAllocation RunFacts)

def metadataWordLimit (bits : Nat) : Nat := 2 ^ bits - 1

theorem metadata_le_wordLimit {bits value : Nat} (h : Fits bits value) : value ≤ metadataWordLimit bits := by
  unfold Fits metadataWordLimit at *
  omega

theorem metadata_wordLimit_fits (bits : Nat) : Fits bits (metadataWordLimit bits) := by
  unfold Fits metadataWordLimit
  exact Nat.sub_lt (pow_pos (by decide : 0 < (2 : Nat)) bits) (by decide : 0 < (1 : Nat))

theorem rawCardData_cachedNode (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (state : NatState) (data : RawCardData q full CB state) (node : (prepareNormalization q full).indexed.NodeId) :
    PA06A19PrepareBankNodeBit022.CachedNode q full CB node state := data.ordered node

/-- Real all-prefix query safety on the exact original allocation. The
ord-room and heap-width hypotheses of frozen022 are discharged internally.
Only the actual fixed containing-code position/PC and entry registers remain. -/
theorem nodeBit_actual_runFacts (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : ScanQueryCodeAt containing start)
    (before : NatState) (data : RawCardData q full (actualControlBase q full) before)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hpc : before.pc = 5 * start) (ha : before.halted = false)
    (hn : before.register .old = node.val) (ht : before.register .fresh = tool.val)
    (hCB : before.register .address = actualControlBase q full)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 46))) :
    ∃ clock ≤ 35,
      PA06A19PrepareBankNodeBit022.NatResult 32 q full containing start (actualAllocation q full) before node tool clock ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have htM := prepared_indexed_size_le q full
  have hnM : node.val < preparedSize q full := node.isLt
  have hord : PA06A19PrepareBankNodeBit022.ordAddress full.length q (actualControlBase q full) node.val < actualAllocation q full := by
    have h := room.1
    unfold PA06A19PrepareBankNodeBit022.ordAddress PA06A19PrepareChildrenCache023.highCacheEnd at *
    change preparedSize q full ≤ mass q full at htM
    change actualControlBase q full + 532 + 2 * mass q full + node.val < actualAllocation q full
    omega
  obtain ⟨clock, hclock, result⟩ := PA06A19PrepareBankNodeBit022.nat_query 32 q full (by decide)
    containing start code (actualControlBase q full) (actualAllocation q full) node tool before
    hpc ha hn ht hCB (rawCardData_cachedNode q full _ before data node) hr hord room.2.1 hend
  refine ⟨clock, hclock, result, ?_, result.prefix_address⟩
  constructor
  · intro count hc
    have h := result.prefix_safe count hc
    refine ⟨fun reg => metadata_le_wordLimit (h.1 reg), h.2.2.1, ?_⟩
    by_cases hlt : count < clock
    · obtain ⟨index, hi, hp, _access⟩ := h.2.2.2 hlt
      exact ⟨index, hi.le, hp⟩
    · have he : count = clock := by omega
      subst count
      exact ⟨start + 46, code.1, result.pc⟩
  · intro count hc
    obtain ⟨index, hi, hp, access⟩ := (result.prefix_safe count hc.le).2.2.2 hc
    exact ⟨index, hi, hp, access⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
