module

public import Structure.PA06_A19Prepare_StaticMetadata036_Cards

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (loadRel storeRel setRel incrementRel)

inductive CardsChunk where
  | initialize | test | body | tail
  deriving DecidableEq

def cardsChunkCode (start : Nat) : CardsChunk → List PackingOp
  | .initialize => setRel 19 0
  | .test => scanBoundedTest 2 19 (start + 84)
  | .body => cardsBody
  | .tail => cardsTail start

def cardsChunkOffset : CardsChunk → Nat
  | .initialize => 0 | .test => 4 | .body => 13 | .tail => 73

def cardsChunkLength : CardsChunk → Nat
  | .initialize => 4 | .test => 9 | .body => 60 | .tail => 11

def cardsChunkLead (start : Nat) (chunk : CardsChunk) : List PackingOp :=
  (cardsChunkCode start chunk).take (cardsChunkLength chunk - 1)
def cardsChunkLast (start : Nat) (chunk : CardsChunk) : PackingOp :=
  (cardsChunkCode start chunk).getD (cardsChunkLength chunk - 1) scanPaddingOp

theorem cards_chunk_length (start : Nat) (chunk : CardsChunk) :
    (cardsChunkCode start chunk).length = cardsChunkLength chunk := by cases chunk <;> rfl

theorem cards_chunk_span (chunk : CardsChunk) : cardsChunkOffset chunk + cardsChunkLength chunk ≤ 84 := by
  cases chunk <;> decide

theorem cards_chunk_lead_length (start : Nat) (chunk : CardsChunk) :
    (cardsChunkLead start chunk).length + 1 = cardsChunkLength chunk := by cases chunk <;> rfl

theorem cards_chunk_split (start : Nat) (chunk : CardsChunk) :
    cardsChunkCode start chunk = cardsChunkLead start chunk ++ [cardsChunkLast start chunk] := by cases chunk <;> rfl

theorem cards_chunk_slice (start : Nat) (chunk : CardsChunk) (position : Nat) (hp : position < cardsChunkLength chunk) :
    (cardsProgramAt start).getD (cardsChunkOffset chunk + position) scanPaddingOp =
      (cardsChunkCode start chunk).getD position scanPaddingOp := by
  cases chunk <;> dsimp only [cardsChunkLength] at hp <;> interval_cases position <;> rfl

theorem cards_chunk_lead_noJump (start : Nat) (chunk : CardsChunk) :
    ∀ op ∈ cardsChunkLead start chunk, NoJump op := by
  cases chunk with
  | body =>
    intro op hm
    exact cardsBody_noJump op (List.mem_of_mem_take hm)
  | «initialize» | test | tail =>
    simp [cardsChunkLead, cardsChunkCode, cardsChunkLength, scanBoundedTest, cardsTail,
      setRel, storeRel, loadRel, incrementRel, jumpTo, NoJump]

def CardsCodeAt (containing : List PackingOp) (start : Nat) : Prop :=
  start + 84 ≤ containing.length ∧ ∀ position < 84,
    containing.getD (start + position) scanPaddingOp = (cardsProgramAt start).getD position scanPaddingOp

theorem cards_append_code (left right : List PackingOp) :
    CardsCodeAt (left ++ cardsProgramAt left.length ++ right) left.length := by
  constructor
  · simp only [List.length_append, cardsProgramAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ cardsProgramAt left.length) right scanPaddingOp _
      (by simp only [List.length_append, cardsProgramAt_length]; omega),
      List.getD_append_right left (cardsProgramAt left.length) scanPaddingOp _ (by omega),
      Nat.add_sub_cancel_left]

theorem cards_chunk_run_prefix (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : CardsCodeAt containing start) (chunk : CardsChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + cardsChunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ cardsChunkLength chunk) :
    natRun rom containing count state = runOps rom ((cardsChunkCode start chunk).take count) state := by
  rw [cards_chunk_split start chunk]
  refine natRun_segment_prefix rom containing (cardsChunkLead start chunk) (cardsChunkLast start chunk)
    (start + cardsChunkOffset chunk)
    (by have hs := cards_chunk_span chunk; have hl := cards_chunk_lead_length start chunk; have hb := code.1; omega)
    ?_ ?_ (cards_chunk_lead_noJump start chunk) state hpc ha count
    (by have hl := cards_chunk_lead_length start chunk; omega)
  · intro position hp
    have hlen := cards_chunk_lead_length start chunk
    have hpos : position < cardsChunkLength chunk := by omega
    have hh := (code.2 (cardsChunkOffset chunk + position) (by have hs := cards_chunk_span chunk; omega)).trans
      (cards_chunk_slice start chunk position hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := cards_chunk_span chunk; have hb := code.1; omega),
      List.getD_eq_getElem _ _ (by rw [cards_chunk_length]; exact hpos)] at hh
    simpa only [Nat.add_assoc, cardsChunkLead, List.getElem_take] using hh
  · have hlen := cards_chunk_lead_length start chunk
    have hpos : (cardsChunkLead start chunk).length < cardsChunkLength chunk := by omega
    have hh := (code.2 (cardsChunkOffset chunk + (cardsChunkLead start chunk).length)
      (by have hs := cards_chunk_span chunk; omega)).trans (cards_chunk_slice start chunk _ hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := cards_chunk_span chunk; have hb := code.1; omega)] at hh
    have heq : (cardsChunkLead start chunk).length = cardsChunkLength chunk - 1 := by omega
    simpa only [Nat.add_assoc, heq, cardsChunkLast] using hh

theorem cards_chunk_run (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : CardsCodeAt containing start) (chunk : CardsChunk) (state : NatState)
    (hpc : state.pc = 5 * (start + cardsChunkOffset chunk)) (ha : state.halted = false) :
    natRun rom containing (cardsChunkLength chunk) state = runOps rom (cardsChunkCode start chunk) state := by
  rw [cards_chunk_run_prefix rom containing start code chunk state hpc ha _ le_rfl,
    List.take_of_length_le (by rw [cards_chunk_length])]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
