module

public import Structure.PSTR_HD_HeadsZeroQueryContract_122

/-! Original ReplyCorrect is a statement about actual Word.toNat reply
registers. Applying ofNat recovers the exact actual Word registers, with no
extra rank/tool Fits assumption. This is the thin physical bridge needed by
both actual query producers; no query/run/heap operation is introduced. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine

theorem original_reply_word_fields {bits q : Nat} (capWords : Nat) (answer : IndexedQuery.Reply q)
    (state : WordState bits) (correct : ReplyCorrect q answer (replyState q capWords state)) :
    state.register .value = BitVec.ofNat bits (encodeRank q answer.rank) ∧
    state.register .old = BitVec.ofNat bits (encodeRank q answer.good) ∧
    state.register .fresh = BitVec.ofNat bits (encodeRank q answer.bad) ∧
    state.register .index = BitVec.ofNat bits (match answer.tool with | none => 0 | some tool => tool.val + 1) := by
  refine ⟨by simpa only [replyState, BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) correct.1,
    by simpa only [replyState, BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) correct.2.1,
    by simpa only [replyState, BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) correct.2.2.1,
    ?_⟩
  cases ht : answer.tool <;>
    simpa only [replyState, ht, BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) correct.2.2.2

theorem internal_query_exit_of_original_reply {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (capWords : Nat) (queryBody : List PackingOp) (stage : Nat) (hs : stage ≤ full.length) (after : WordState bits)
    (hp : after.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : after.halted = false)
    (correct : ReplyCorrect q (callback q full ⟨stage, callback_stage_bound full stage hs⟩ used) (replyState q capWords after)) :
    InternalQueryExit full used queryBody stage hs after := by
  have words := original_reply_word_fields capWords _ after correct
  exact ⟨hp, ha, words.1, words.2.2.1⟩

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
