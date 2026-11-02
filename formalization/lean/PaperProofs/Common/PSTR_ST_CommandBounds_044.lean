module

public import PaperProofs.Common.PSTR_ST_SharpUpperClaims_043

/-! Exact finite-list and physical-word bounds for the ORIGINAL hybrid
commands and query-record function. These do not assume or establish a
machine implementation, reply correctness or an actual command script. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics.CompactABI

open PaperProofs.Structure.LaminarTree
open AlgorithmClaims

variable {I : Instance}

theorem commandsAt_length (history : List (VisibleEvent I)) :
    (CompactPrice.commandsAt I history).length =
      2 * min (historyCursor history) I.stageCount +
        (if historyCursor history < I.stageCount then 1 else 0) := by
  classical
  by_cases hcursor : historyCursor history < I.stageCount
  · simp [CompactPrice.commandsAt, List.length_flatMap, Nat.mul_comm, hcursor]
  · simp [CompactPrice.commandsAt, List.length_flatMap, Nat.mul_comm, hcursor]

theorem commandsAt_length_le (history : List (VisibleEvent I)) :
    (CompactPrice.commandsAt I history).length ≤ 2 * I.stageCount + 1 := by
  rw [commandsAt_length]
  have hmin := Nat.min_le_right (historyCursor history) I.stageCount
  split_ifs <;> omega

theorem queryRecords_length_le {bits q : Nat} (full : List (Finset (Fin q)))
    (program : List PackingOp) (commands : List CompactControllerClaims.Command)
    (counts : List Nat) (heap : BitVec bits → BitVec bits) :
    (CompactPrice.queryRecords q full program commands counts heap).length ≤ 4 * commands.length := by
  induction commands generalizing counts heap with
  | nil => simp [CompactPrice.queryRecords]
  | cons command later ih =>
    cases counts with
    | nil => simp [CompactPrice.queryRecords]
    | cons steps counts =>
      let result := packingRun (CompactControllerClaims.callInput q full command)
        program steps (packingInitial heap)
      have htail := ih counts result.heap
      change ((if command = .query then
        [(result.register .value).toNat, (result.register .old).toNat,
          (result.register .fresh).toNat, (result.register .index).toNat] else []) ++
          CompactPrice.queryRecords q full program later counts result.heap).length ≤ _
      rw [List.length_append]
      split_ifs <;> simp only [List.length_cons, List.length_nil] <;> omega

theorem queryRecords_wordBound {bits q : Nat} (full : List (Finset (Fin q)))
    (program : List PackingOp) (commands : List CompactControllerClaims.Command)
    (counts : List Nat) (heap : BitVec bits → BitVec bits) :
    ∀ word ∈ CompactPrice.queryRecords q full program commands counts heap, word < 2 ^ bits := by
  induction commands generalizing counts heap with
  | nil => simp [CompactPrice.queryRecords]
  | cons command later ih =>
    cases counts with
    | nil => simp [CompactPrice.queryRecords]
    | cons steps counts =>
      let result := packingRun (CompactControllerClaims.callInput q full command)
        program steps (packingInitial heap)
      intro word hword
      change word ∈ (if command = .query then
        [(result.register .value).toNat, (result.register .old).toNat,
          (result.register .fresh).toNat, (result.register .index).toNat] else []) ++
          CompactPrice.queryRecords q full program later counts result.heap at hword
      rcases List.mem_append.mp hword with hhead | htail
      · by_cases hquery : command = .query
        · simp only [hquery, ite_true, List.mem_cons, List.not_mem_nil, or_false] at hhead
          rcases hhead with rfl | rfl | rfl | rfl
          · exact (result.register .value).isLt
          · exact (result.register .old).isLt
          · exact (result.register .fresh).isLt
          · exact (result.register .index).isLt
        · simp only [hquery, ite_false, List.not_mem_nil] at hhead
      · exact ih counts result.heap word htail

theorem actualQueryRecords_length_le {bits : Nat} (history : List (VisibleEvent I))
    (program : List PackingOp) (counts : List Nat) (heap : BitVec bits → BitVec bits) :
    (CompactPrice.queryRecords I.toolCount I.compatibility program
      (CompactPrice.commandsAt I history) counts heap).length ≤ 4 * (2 * I.stageCount + 1) :=
  (queryRecords_length_le I.compatibility program (CompactPrice.commandsAt I history) counts heap).trans
    (Nat.mul_le_mul_left 4 (commandsAt_length_le history))

end PaperProofs.Common.Native.PSTRStatistics.CompactABI
