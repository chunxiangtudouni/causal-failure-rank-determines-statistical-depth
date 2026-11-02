module

public import Structure.PA06_A19Prepare_AllQCode082_Program

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
set_option maxRecDepth 30000

/-! UNVALIDATED finite per-op check of the actual patched1639-op prefix.
The dispatcher literal includes this whole program's zero-handler tail.
The finite budget is the same as052; it is not raised after a failure. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

private theorem dispatcher_gate_encoded_words_fit32 (length : Nat)
    (room : Fits 32 (5 * (RawIncidenceLaminarRAM.checker.length + 2 + length))) :
    WordsFit 32 (packingCode (RawIncidenceLaminarRAM.dispatcherGate length)) := by
  intro value hv
  simp [packingCode, RawIncidenceLaminarRAM.dispatcherGate, PackingOp.encode,
    Op.encodeWords, Instruction.encodeWords, Register.word, haltWords] at hv
  change value < 2 ^ 32
  change 5 * (RawIncidenceLaminarRAM.checker.length + 2 + length) < 2 ^ 32 at room
  omega

private theorem early_head_encoded_words_fit32 (handlerPC : Nat)
    (room : Fits 32 handlerPC) :
    WordsFit 32 (packingCode (PA06A19PrepareEarlyGate079.head handlerPC)) := by
  intro value hv
  simp [packingCode, PA06A19PrepareEarlyGate079.head,
    PA06A19PrepareEarlyGate079.lead, PA06A19PrepareEarlyGate079.branch,
    PA06A19PrepareEarlyGate079.restore, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, Register.word, Region.word, haltWords] at hv
  change value < 2 ^ 32
  change handlerPC < 2 ^ 32 at room
  omega

theorem prefix_encoded_words_fit32 : WordsFit 32 (packingCode patchedPrefix) := by
  -- The exact dispatcher constructor includes the complete real tail.
  let dispatcherBody : List PackingOp :=
    PA06A19PrepareCompactInit006.initProgram ++
      (RawCandidateRetentionRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.retentionStart ++
        (RawCandidateOrderingRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.orderingStart ++
          (RawCandidateParentRAM.programAt PA06A19PrepareCompactCandidates007.parentStart ++
            PA06A19PrepareRawHeader039Entry.headerSuffix
              (PA06A19PrepareRawSequence043.suffix
                (PA06A19PreparePreBuild044.suffix
                  (PA06A19PreparePostDP055.tail (PA06A19PrepareRawActive076.bodyTail right)))))))
  have endLength : RawIncidenceLaminarRAM.checker.length + 2 + dispatcherBody.length = finalEnd := by
    have fullLength := oldP_length
    change (RawIncidenceLaminarRAM.dispatcherProgram dispatcherBody).length = finalEnd at fullLength
    simpa only [RawIncidenceLaminarRAM.dispatcherProgram_length] using fullLength
  -- Check the complete endpoint once, instead of inside every encoded op.
  have finalRoom : Fits 32 (5 * finalEnd) := by
    change 5 * finalEnd < 2 ^ 32
    decide
  have handlerLe : handlerStart ≤ finalEnd := by
    unfold finalEnd
    exact Nat.le_add_right _ _
  have handlerRoom : Fits 32 (5 * handlerStart) :=
    (Nat.mul_le_mul_left 5 handlerLe).trans_lt finalRoom
  have gateRoom : Fits 32 (5 * (RawIncidenceLaminarRAM.checker.length + 2 + dispatcherBody.length)) := by
    rw [endLength]
    exact finalRoom
  have gateFit := dispatcher_gate_encoded_words_fit32 dispatcherBody.length gateRoom
  have headFit := early_head_encoded_words_fit32 (5 * handlerStart) handlerRoom
  have checkerRestFit : WordsFit 32 (packingCode (RawIncidenceLaminarRAM.checker.drop 10)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have patchedCheckerFit : WordsFit 32
      (packingCode (PA06A19PrepareEarlyGate079.program (5 * handlerStart) RawIncidenceLaminarRAM.checker)) := by
    simpa only [PA06A19PrepareEarlyGate079.program] using
      (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ headFit checkerRestFit)
  have initFit : WordsFit 32 (packingCode PA06A19PrepareCompactInit006.initProgram) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have retentionFit : WordsFit 32
      (packingCode (RawCandidateRetentionRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.retentionStart)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have orderingFit : WordsFit 32
      (packingCode (RawCandidateOrderingRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.orderingStart)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have parentFit : WordsFit 32
      (packingCode (RawCandidateParentRAM.programAt PA06A19PrepareCompactCandidates007.parentStart)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have headerFit : WordsFit 32
      (packingCode (PA06A19PrepareRawHeader039Body.headerProgram PA06A19PrepareRawHeader039Entry.headerStart)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have runtimeFit : WordsFit 32 (packingCode (PA06A19PrepareRuntimeLayout026.sequence 1310)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have childrenFit : WordsFit 32 (packingCode (PA06A19PrepareChildrenCache023.programAt 1444)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  have clearFit : WordsFit 32 (packingCode (PA06A19PrepareClearVM045.programAt 1588)) := by
    apply PA06A19PrepareCodeFit052.encoded_words_fit32_of_checked
    decide
  let rest : List PackingOp :=
    RawIncidenceLaminarRAM.dispatcherGate dispatcherBody.length ++
      PA06A19PrepareCompactInit006.initProgram ++
      RawCandidateRetentionRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.retentionStart ++
      RawCandidateOrderingRAM.programAt PA06A19PrepareCompactCandidates007.Metadata.orderingStart ++
      RawCandidateParentRAM.programAt PA06A19PrepareCompactCandidates007.parentStart ++
      PA06A19PrepareRawHeader039Body.headerProgram PA06A19PrepareRawHeader039Entry.headerStart ++
      PA06A19PrepareRuntimeLayout026.sequence 1310 ++
      PA06A19PrepareChildrenCache023.programAt 1444 ++
      PA06A19PrepareClearVM045.programAt 1588
  have restFit : WordsFit 32 (packingCode rest) := by
    simpa only [rest, List.append_assoc] using
      (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ gateFit
        (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ initFit
          (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ retentionFit
            (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ orderingFit
              (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ parentFit
                (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ headerFit
                  (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ runtimeFit
                    (PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ childrenFit clearFit))))))))
  have oldLayout : oldPrefix = RawIncidenceLaminarRAM.checker ++ rest := by
    simp only [oldPrefix, PA06A19PrepareRawActive076.front, PA06A19PreparePostDP055.front,
      PA06A19PreparePreBuild044.clearFront, PA06A19PreparePreBuild044.rawFront,
      PA06A19PrepareRawSequence043.front, PA06A19PrepareRawHeader039Entry.front,
      PA06A19PrepareCompactCandidates007.parentFront,
      PA06A19PrepareCompactCandidates007.Metadata.orderingFront,
      PA06A19PrepareCompactCandidates007.Metadata.front, dispatcherBody, rest,
      List.append_assoc]
  have checkerRoom : 10 ≤ RawIncidenceLaminarRAM.checker.length := by
    rw [RawIncidenceLaminarRAM.checker_length]
    decide
  rw [patchedPrefix, oldLayout, patch_append _ _ _ checkerRoom]
  exact PA06A19PrepareCodeFit052.append_encoded_words_fit _ _ patchedCheckerFit restFit

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082
