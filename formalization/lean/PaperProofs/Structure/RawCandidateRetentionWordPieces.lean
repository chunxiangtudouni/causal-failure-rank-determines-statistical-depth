module

public import PaperProofs.Structure.RawCandidateRetentionWordBounds
public import PaperProofs.Structure.RawCandidateRetentionWordDataPieces
public import PaperProofs.Structure.RawCandidateRetentionWordSafety

/-! Every actual small retention piece is safe from precisely its ordinary
source-cell bounds.  The loop proof must establish Needs at each runtime
boundary; no retention/keep result or whole-loop safety is a premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordPieces

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateRetentionRAM
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateWorkspaceInit (workspaceBase candidateCount candidateCount_fits)
open RawCandidateWorkspaceBounds (workspaceLimit)
open RawCandidateRetentionWordChunks (Chunk chunkCode chunkLength chunkOffset)
open RawCandidateRetentionWordBounds (Needs)

theorem prefix_fit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (chunk : Chunk) (state : NatState)
    (hr : RegistersFit (indexWidth 16 full.length q) state) (hn : Needs q full chunk state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398)))
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state) := by
  cases chunk with
  | «initialize» =>
    exact RawCandidateWorkspaceWordMacros.set_prefix_fit q full 1 0 (by decide) state hr hn.1
      (RawCandidateWorkspaceWordMacros.small_constant_fits _ _ _ (by decide)) count hc
  | outerTest =>
    have hM : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q)) := by
      rw [hn.2.1]; exact candidateCount_fits _ _
    exact RawCandidateWorkspaceWordMacros.test_prefix_fit q full 1 (start + 398) (by decide) state hr hn.1
      hM (hn.2.2.trans_lt (candidateCount_fits _ _)) hend count hc
  | cardArgs => exact RawCandidateRetentionWordBounds.cardArgs_prefix_fit q full state hr hn.1 hn.2 count hc
  | afterCard => exact RawCandidateRetentionWordDataPieces.afterCard_prefix_fit q full state hr hn.1 hn.2.1 hn.2.2 count hc
  | innerTest =>
    have hM : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q)) := by
      rw [hn.2.1]; exact candidateCount_fits _ _
    have he : Fits (indexWidth 16 full.length q) (5 * (start + 364)) := lt_of_le_of_lt (by omega) hend
    exact RawCandidateWorkspaceWordMacros.test_prefix_fit q full 2 (start + 364) (by decide) state hr hn.1
      hM (hn.2.2.trans_lt (candidateCount_fits _ _)) he count hc
  | pairArgs => exact RawCandidateRetentionWordBounds.pairArgs_prefix_fit q full state hr hn.1 hn.2.1 hn.2.2 count hc
  | innerTail =>
    exact RawCandidateRetentionWordDataPieces.innerTail_prefix_fit q full start state hr hn.1
      hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 hend count hc
  | finish =>
    exact RawCandidateRetentionWordDataPieces.finishCandidate_prefix_fit q full start state hr hn.1
      hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 hend count hc

theorem prefix_access (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (chunk : Chunk) (state : NatState)
    (hn : Needs q full chunk state) (count : Nat) (hc : count < chunkLength chunk) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)
      ((chunkCode start chunk).getD count paddingOp) := by
  cases chunk with
  | «initialize» => exact RawCandidateWorkspaceWordMacros.set_prefix_access q full 1 0 (by decide) state hn.1 count hc
  | outerTest => exact RawCandidateWorkspaceWordMacros.test_prefix_access q full 1 (start + 398) (by decide) state hn.1 count hc
  | cardArgs => exact RawCandidateRetentionWordBounds.cardArgs_prefix_access q full state hn.1 count hc
  | afterCard => exact RawCandidateRetentionWordDataPieces.afterCard_prefix_access q full state hn.1 hn.2.1 count hc
  | innerTest => exact RawCandidateWorkspaceWordMacros.test_prefix_access q full 2 (start + 364) (by decide) state hn.1 count hc
  | pairArgs => exact RawCandidateRetentionWordBounds.pairArgs_prefix_access q full state hn.1 count hc
  | innerTail => exact RawCandidateRetentionWordDataPieces.innerTail_prefix_access q full start state hn.1 count hc
  | finish => exact RawCandidateRetentionWordDataPieces.finishCandidate_prefix_access q full start state hn.1 hn.2.1 hn.2.2.1 count hc

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 398 ≤ containing.length)
  (hcode : ∀ position < 398, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem piece_run (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing (chunkLength chunk) state =
      runOps (rawIncidenceROM q full) (chunkCode start chunk) state := by
  rw [RawCandidateRetentionWordChunks.chunk_run_prefix _ containing start hbound hcode chunk state hpc ha
    (chunkLength chunk) le_rfl,
    List.take_of_length_le (by rw [RawCandidateRetentionWordChunks.chunk_code_length])]

theorem piece_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hr : RegistersFit (indexWidth 16 full.length q) state) (hn : Needs q full chunk state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 398))) :
    PrefixSafe (RawCandidateRetentionWordSafety.SafePoint q full containing start) (rawIncidenceROM q full)
      containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  exact RawCandidateRetentionWordSafety.chunk_safe q full containing start hbound hcode chunk state hpc ha
    (fun count hc => prefix_fit q full start chunk state hr hn hend count hc)
    (fun count hc => prefix_access q full start chunk state hn count hc)

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateRetentionWordPieces
