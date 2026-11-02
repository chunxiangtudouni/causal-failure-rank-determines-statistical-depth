module

public import Structure.PSTR_LiveHistory_142

/-! Actual four-word records equal the OLD callback specification at each
original command configuration. The specification is a conclusion of the
actual physical runs, not a rank/eligibility input to the Boolean planner. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRQueryRecords

open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def registerWords {bits : Nat} (state : WordState bits) : List Nat :=
  [(state.register .value).toNat, (state.register .old).toNat,
    (state.register .fresh).toNat, (state.register .index).toNat]

noncomputable def replyWords (q : Nat) (answer : IndexedQuery.Reply q) : List Nat :=
  [encodeRank q answer.rank, encodeRank q answer.good, encodeRank q answer.bad,
    match answer.tool with | none => 0 | some tool => tool.val + 1]

theorem allowed_stage_bound {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (command : Command) (allowed : Allowed full configuration command) :
    configuration.stage < full.length + 1 := by
  cases command with
  | query => exact Nat.lt_succ_of_le allowed.2
  | correct => exact Nat.lt_succ_of_lt allowed.2
  | error => exact Nat.lt_succ_of_lt allowed.2

noncomputable def semanticRecords {q : Nat} (full : List (Finset (Fin q))) :
    (configuration : Configuration q) → (commands : List Command) →
    PSTRCommandPrefixes.AllowedSequence full configuration commands → List Nat
  | _, [], _ => []
  | configuration, command :: later, allowed =>
    (if command = .query then
      replyWords q (callback q full
        ⟨configuration.stage, allowed_stage_bound full configuration command allowed.1⟩ configuration.used)
      else []) ++
      semanticRecords full (nextConfiguration q full configuration command) later allowed.2

theorem registerWords_of_call {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (configuration : Configuration q) (command : Command) (steps : Nat)
    (heap : BitVec bits → BitVec bits) (cursor : configuration.stage < full.length + 1)
    (call : CallClaims constant q full capWords heapWords program configuration command steps heap) :
    registerWords (packingRun (callInput q full command) program steps (packingInitial heap)) =
      replyWords q (callback q full ⟨configuration.stage, cursor⟩ configuration.used) := by
  have reply := call.2.2.2.2.2 cursor
  unfold registerWords replyWords
  exact congrArg₂ List.cons reply.1 (congrArg₂ List.cons reply.2.1
    (congrArg₂ List.cons reply.2.2.1 (congrArg₂ List.cons reply.2.2.2 rfl)))

theorem records_of_run {bits q constant capWords heapWords : Nat}
    (full : List (Finset (Fin q))) (program : List PackingOp)
    (configuration : Configuration q) (commands : List Command) (counts : List Nat)
    (heap : BitVec bits → BitVec bits)
    (execution : CommandsRunClaims constant q full capWords heapWords program configuration commands counts heap) :
    CompactPrice.queryRecords q full program commands counts heap =
      semanticRecords full configuration commands
        (PSTRCommandPrefixes.allowed_of_run full program configuration commands counts heap execution) := by
  induction commands generalizing configuration counts heap with
  | nil => rfl
  | cons command later ih =>
    cases counts with
    | nil => exact False.elim execution
    | cons steps counts =>
      let after := packingRun (callInput q full command) program steps (packingInitial heap)
      have head := registerWords_of_call full program configuration command steps heap
        (allowed_stage_bound full configuration command execution.1) execution.2.1
      have tail := ih (nextConfiguration q full configuration command) counts after.heap execution.2.2
      change (if command = .query then registerWords after else []) ++
          CompactPrice.queryRecords q full program later counts after.heap =
        (if command = .query then replyWords q (callback q full
          ⟨configuration.stage, allowed_stage_bound full configuration command execution.1⟩ configuration.used) else []) ++
          semanticRecords full (nextConfiguration q full configuration command) later _
      rw [head, tail]

end PaperProofs.Common.Native.PSTRQueryRecords
