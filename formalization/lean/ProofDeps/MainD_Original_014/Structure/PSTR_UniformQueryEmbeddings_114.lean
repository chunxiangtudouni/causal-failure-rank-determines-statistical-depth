module

public import Structure.PSTR_UniformQueryCode_113
public import Structure.PA17_A19QueryBridge_RuntimeRelocate_029b

/-! Five real constituent embeddings at the NEW literal labels. These are
code facts; no old539/1340 execution theorem is shifted or renamed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformQueryEmbeddings

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRUniformQueryCode

theorem header_in {bits : Nat} (whole : List PackingOp) (contains : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hp : Fits bits (5 * whole.length)) :
    PA17A19RuntimeRelocate029.CodeAt bits 63 whole := by
  have h := block_in whole contains 541 _ header_block
  exact ⟨h.bound, h.code, hw, hp⟩

theorem tests_in {bits : Nat} (whole : List PackingOp) (contains : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hp : Fits bits (5 * whole.length)) :
    PA17A19RuntimeTests010.Embedded bits 623 whole := by
  have h := block_in whole contains 623 _ tests_block
  exact ⟨h.bound, h.code, hw, hp⟩

theorem ranks_in {bits : Nat} (whole : List PackingOp) (contains : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hp : Fits bits (5 * whole.length)) :
    PA17A19RuntimeRanks008.Embedded bits 978 whole := by
  have h := block_in whole contains 978 _ ranks_block
  exact ⟨h.bound, h.code, hw, hp⟩

theorem selector_in {bits : Nat} (whole : List PackingOp) (contains : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hp : Fits bits (5 * whole.length)) :
    PA17A19RuntimeSelect009.CoreEmbedded bits 1029 whole := by
  have h := block_in whole contains 1029 _ selector_block
  exact ⟨h.bound, h.code, hw, hp⟩

theorem reply_in {bits : Nat} (whole : List PackingOp) (contains : Contains whole)
    (hw : WordsFit bits (packingCode whole)) (hp : Fits bits (5 * whole.length)) :
    PA17A19RuntimeReply016.Embedded bits 1310 whole := by
  have h := block_in whole contains 1310 _ reply_block
  exact ⟨h.bound, h.code, hw, hp⟩

theorem word_room (N q : Nat) : Fits (indexWidth 32 N q) 8192 := by
  have hb := PSTROriginalCountRoom.word_lower N q
  have hp : 2 ^ 32 ≤ 2 ^ indexWidth 32 N q := Nat.pow_le_pow_right (by decide) hb
  exact (by decide : 8192 < 2 ^ 32).trans_le hp

theorem program_words (N q : Nat) : WordsFit (indexWidth 32 N q) (packingCode program) :=
  code_fit (word_room N q)

theorem program_pc (N q : Nat) : Fits (indexWidth 32 N q) (5 * program.length) :=
  pc_fit (word_room N q)

theorem from_counts {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (allowed : Allowed full configuration command)
    (hq : 0 < q) (hl : LaminarSchedule full) (whole : List PackingOp) (contains : Contains whole)
    (hw : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hp : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (complete : PSTRCountComplete.Complete full configuration 63
      (capacityWords 8192 full.length q (treeSize q full)) state) :
    PA17A19RuntimeRelocate029.QueryReady full command configuration
      (PA17A19RuntimeEntry020.cursor full configuration command allowed) hq 63 whole state
      (packingRun (callInput q full command) whole (PA17A19RuntimeRelocate029.suffixClock q (treeSize q full)) state) :=
  PA17A19RuntimeRelocate029.from_counts_query full command configuration allowed hq hl whole
    (header_in whole contains hw hp) (tests_in whole contains hw hp) (ranks_in whole contains hw hp)
    (selector_in whole contains hw hp) (reply_in whole contains hw hp) state complete

end PaperProofs.Structure.LaminarTree.PSTRUniformQueryEmbeddings
