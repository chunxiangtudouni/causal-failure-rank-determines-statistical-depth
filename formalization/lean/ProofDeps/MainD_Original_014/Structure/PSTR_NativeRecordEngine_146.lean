module

public import Structure.PSTR_NativeQueryRecords_145

/-! The actual Word engine and its exact OLD record semantics share one
final count list and every original counts.take prefix on the same heap.
No separately supplied execution or rank stream remains in the interface. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRQueryRecords

open PaperProofs.Structure.LaminarTree
open AlgorithmClaims CompactControllerClaims PA17A19RuntimeEntry020

variable {I : Instance}

theorem actual_horizon_halted (input : StatisticalInput I) (C : Contract I)
    (current : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : Nat)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent)))
    (sample : Unit × input.World) :
    (run input C .native accounting policy.rule sample
      (quotaActionBound I (referenceQuota input exponent) + 1)).halted = true := by
  rw [PA17L01HistoryPrefixActual004.native_table_run_eq input C accounting available budget
    (some (referenceQuota input exponent)) policy hrule sample]
  exact PSTRStatistics.tableRule_halted input C current.1 accounting available budget
    (referenceQuota input exponent) sample

theorem actual_native_engine (input : StatisticalInput I) (C : Contract I)
    (hl : LaminarSchedule I.compatibility) (current : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (delta : ℝ)
    (budget : ℚ) (exponent : Nat) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (policy : Policy input C .native accounting Unit)
    (hrule : policy.rule = CompactPrice.tableRule input available budget (some (referenceQuota input exponent)))
    (heap : BitVec (wordBits I.compatibility) → BitVec (wordBits I.compatibility))
    (rep : HeapRepresents I.toolCount I.compatibility (capacity I.compatibility)
      ⟨0, Finset.univ \ available, false⟩ heap)
    (sample : Unit × input.World) (horizon : Nat) :
    let history := (run input C .native accounting policy.rule sample horizon).history
    let commands := CompactPrice.commandsAt I history
    ∃ counts : List Nat,
      counts.length = commands.length ∧ commands.length ≤ 2 * I.stageCount + 1 ∧
      CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility)
        (allocatedWords I.compatibility) PSTRLiveControllerCode.program
        ⟨0, Finset.univ \ available, false⟩ commands counts heap ∧
      commandsCost I.toolCount I.compatibility PSTRLiveControllerCode.program commands counts heap ≤
        65536 * (I.stageCount + 1) * liveWork I.toolCount (treeSize I.toolCount I.compatibility) ∧
      CompactPrice.queryRecords I.toolCount I.compatibility PSTRLiveControllerCode.program
        commands counts heap = nativeRecords available history ∧
      ∀ clock : Fin horizon,
        let prefixHistory := (run input C .native accounting policy.rule sample clock.val).history
        let prefixCommands := CompactPrice.commandsAt I prefixHistory
        let records := CompactPrice.queryRecords I.toolCount I.compatibility PSTRLiveControllerCode.program
          prefixCommands (counts.take prefixCommands.length) heap
        prefixCommands.IsPrefix commands ∧
        CommandsRunClaims 65536 I.toolCount I.compatibility (capacity I.compatibility)
          (allocatedWords I.compatibility) PSTRLiveControllerCode.program
          ⟨0, Finset.univ \ available, false⟩ prefixCommands (counts.take prefixCommands.length) heap ∧
        records = nativeRecords available prefixHistory ∧
        records.length ≤ 4 * (2 * I.stageCount + 1) ∧
        ∀ word ∈ records, word < 2 ^ wordBits I.compatibility := by
  obtain ⟨counts, countsLength, length, execution, cost, prefixes⟩ :=
    PSTRLiveHistory.actual_native_words input C hl current accounting available delta budget exponent
      choice policy hrule heap rep sample horizon
  refine ⟨counts, countsLength, length, execution, cost, ?_, ?_⟩
  · exact actual_native_records input C hl current accounting available delta budget exponent choice
      policy hrule PSTRLiveControllerCode.program sample horizon counts heap execution
  · intro clock
    obtain ⟨isPrefixFact, prefixExecution, recordLength, recordWords⟩ := prefixes clock
    refine ⟨isPrefixFact, prefixExecution, ?_, recordLength, recordWords⟩
    exact actual_native_records input C hl current accounting available delta budget exponent choice
      policy hrule PSTRLiveControllerCode.program sample clock.val _ heap prefixExecution

end PaperProofs.Common.Native.PSTRQueryRecords
