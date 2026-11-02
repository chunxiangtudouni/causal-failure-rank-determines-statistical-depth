module

public import Structure.PSTR_NativeRecordEngine_146

/-! The current query occupies exactly the four final words after the
completed stages. The pending current-stage commitment is not inserted
into stageUsed. These are readback theorems, not a Boolean decoder. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRQueryRecords

open PaperProofs.Structure.LaminarTree
open CompactControllerClaims PA17L01HistoryPrefixCommands001 PA17L01HistoryPrefixStrategy002

theorem stageWords_length {q : Nat} (full : List (Finset (Fin q)))
    (used : Nat → Finset (Fin q)) (stage : Nat) (bound : stage ≤ full.length) :
    (stageWords full used stage).length = 4 := by
  rw [stageWords_spec full used stage (by omega)]
  rfl

theorem stageRecords_length {q : Nat} (full : List (Finset (Fin q)))
    (used : Nat → Finset (Fin q)) (first count : Nat) (bound : first + count ≤ full.length) :
    (stageRecords full used first count).length = 4 * count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [stageRecords_succ, List.length_append, stageWords_length full used first (by omega),
      ih (first + 1) (by omega)]
    omega

theorem nativeRecords_current {I : Instance} (available : Finset I.Tool)
    (history : List (VisibleEvent I)) (current : historyCursor history < I.stageCount) :
    (nativeRecords available history).drop (4 * historyCursor history) =
      replyWords I.toolCount
        (callback I.toolCount I.compatibility ⟨historyCursor history, Nat.lt_succ_of_lt current⟩
          (stageUsed available history (historyCursor history))) := by
  have fullLength : I.compatibility.length = I.stageCount := rfl
  have length := stageRecords_length I.compatibility (stageUsed available history)
    0 (historyCursor history) (by rw [fullLength]; omega)
  dsimp only [nativeRecords]
  rw [Nat.min_eq_left (Nat.le_of_lt current), ite_eq_left current,
    stageWords_spec I.compatibility (stageUsed available history) (historyCursor history) (Nat.lt_succ_of_lt current)]
  rw [← length, List.drop_left]

theorem actual_current_record_slice {I : Instance} {bits constant capWords heapWords : Nat}
    (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ)
    (budget : ℚ) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent)))
    (program : List AlgorithmClaims.PackingOp) (sample : Unit × input.World) (clock : Nat)
    (counts : List Nat) (heap : BitVec bits → BitVec bits)
    (execution : CommandsRunClaims constant I.toolCount I.compatibility capWords heapWords program
      ⟨0, Finset.univ \ available, false⟩
      (CompactPrice.commandsAt I (run input C .native accounting policy.rule sample clock).history) counts heap)
    (active : historyCursor (run input C .native accounting policy.rule sample clock).history < I.stageCount) :
    let history := (run input C .native accounting policy.rule sample clock).history
    (CompactPrice.queryRecords I.toolCount I.compatibility program
      (CompactPrice.commandsAt I history) counts heap).drop (4 * historyCursor history) =
      replyWords I.toolCount
        (callback I.toolCount I.compatibility ⟨historyCursor history, Nat.lt_succ_of_lt active⟩
          (stageUsed available history (historyCursor history))) := by
  dsimp only
  rw [actual_native_records input C hl current accounting available delta budget exponent choice
    policy hrule program sample clock counts heap execution]
  exact nativeRecords_current available _ active

end PaperProofs.Common.Native.PSTRQueryRecords
