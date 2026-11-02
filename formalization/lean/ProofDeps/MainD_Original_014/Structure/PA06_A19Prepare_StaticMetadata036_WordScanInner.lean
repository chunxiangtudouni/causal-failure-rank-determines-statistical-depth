module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordScanPairSemantics

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED actual inner scan with one joint witness at every step.
Exactly count real pair iterations are executed, each including its own
tool guard. The exhausted tool guard is not executed by these interfaces;
the original row-finish segment owns that guard and the outer backjump.
No separate existential semantic and safety clocks are combined. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (actualPackedWords actualControlBase actualAllocation RunFacts)

/-- Exactly count actual tools, with the next semantic invariant, heap
frame and every-prefix bounds all attached to the same cumulative clock. -/
theorem scan_inner_partial_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafInnerReady q full (actualControlBase q full) (actualPackedWords q full)
      reference node 0 (5 * (start + 51)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length))
    (count : Nat) (hc : count ≤ q) :
    ∃ clock ≤ 116 * count,
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafInnerReady q full (actualControlBase q full) (actualPackedWords q full)
        reference node count (5 * (start + 51)) after ∧
      ScanFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let B := metadataWordLimit bits
  let H := actualAllocation q full
  revert hc
  induction count with
  | zero =>
    intro _
    have zeroSafe : RunFacts B H rom containing 0 before := by
      constructor
      · constructor
        · intro clock hclock
          have hz : clock = 0 := by omega
          subst clock
          exact ⟨fun reg => metadata_le_wordLimit (hr reg), ready.active,
            start + 51, by have hb := code.1; omega, ready.pc⟩
        · intro clock hclock
          omega
      · intro clock hclock
        have hz : clock = 0 := by omega
        subst clock
        rfl
    exact ⟨0, by omega, ready,
      ScanFrame.refl q full (actualControlBase q full) (actualPackedWords q full) before, zeroSafe⟩
  | succ count ih =>
    intro hc
    obtain ⟨previousClock, previousBound, previousReady, previousFrame, previousSafe⟩ := ih (by omega)
    let previous := natRun rom containing previousClock before
    have previousRegs : RegistersFit bits previous := by
      intro reg
      exact (((previousSafe.1).final _ _ _ _ _).1 reg).trans_lt (metadata_wordLimit_fits bits)
    obtain ⟨nextClock, nextBound, nextNamed, nextReady, nextFrame, nextSafe⟩ :=
      scan_pair_named_witness q full hq reference referenceData containing start code
        node ⟨count, by omega⟩ previous previousReady previousRegs hcodePC
    subst nextClock
    let pairClock := scanPairClock q full (actualControlBase q full) previous node.val count
    have pairBound : pairClock ≤ 116 := nextBound
    have combined : RunFacts B H rom containing (previousClock + pairClock) before :=
      RunFacts.add B H rom containing previousClock pairClock before previousSafe nextSafe
    refine ⟨previousClock + pairClock, ?_, ?_⟩
    · rw [Nat.mul_succ]
      omega
    · refine ⟨?_, ?_, combined⟩
      · rw [natRun_add rom containing previousClock pairClock before]
        exact nextReady
      · rw [natRun_add rom containing previousClock pairClock before]
        exact previousFrame.trans nextFrame

/-- All q pair iterations are complete at the original inner-test PC51.
The real exhausted guard and outer tail remain in the original row finish;
this interface does not count them twice or claim the full191-op run. -/
theorem scan_inner_final_joint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (reference : NatState) (referenceData : RawCardData q full (actualControlBase q full) reference)
    (containing : List PackingOp) (start : Nat) (code : LeafToolCodeAt containing start)
    (node : (prepareNormalization q full).indexed.NodeId) (before : NatState)
    (ready : LeafInnerReady q full (actualControlBase q full) (actualPackedWords q full)
      reference node 0 (5 * (start + 51)) before)
    (hr : RegistersFit (indexWidth 32 full.length q) before)
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 116 * q,
      let after := natRun (rawIncidenceROM q full) containing clock before
      LeafInnerReady q full (actualControlBase q full) (actualPackedWords q full)
        reference node q (5 * (start + 51)) after ∧
      ScanFrame q full (actualControlBase q full) (actualPackedWords q full) before after ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        (rawIncidenceROM q full) containing clock before :=
  scan_inner_partial_joint q full hq reference referenceData containing start code node before ready hr hcodePC q le_rfl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
