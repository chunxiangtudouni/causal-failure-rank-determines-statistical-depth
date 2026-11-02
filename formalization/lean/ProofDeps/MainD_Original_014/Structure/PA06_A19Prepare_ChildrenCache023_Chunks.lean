module

public import Structure.PA06_A19Prepare_ChildrenCache023
public import PaperProofs.Structure.RawIncidenceScanSafety

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled actual fetched prefixes of the fixed144 children
producer. This is the same proven segment-prefix mechanism used by the
original children serializer, at this new smaller actual relative layout. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety

inductive Chunk where
  | initialize | outerTest | initializeRow | innerTest | matchTest | skip | matched | innerTail | outerTail
  deriving DecidableEq

def chunkCode (start : Nat) : Chunk → List PackingOp
  | .initialize => initializeCache
  | .outerTest => boundedTest 64 (start + 144)
  | .initializeRow => initializeRow
  | .innerTest => boundedTest 65 (start + 122)
  | .matchTest => matchTest start
  | .skip => jumpTo (start + 111)
  | .matched => matched
  | .innerTail => innerTail start
  | .outerTail => outerTail start

def chunkOffset : Chunk → Nat
  | .initialize => 0 | .outerTest => 32 | .initializeRow => 41 | .innerTest => 49
  | .matchTest => 58 | .skip => 81 | .matched => 84 | .innerTail => 111 | .outerTail => 122

def chunkLength : Chunk → Nat
  | .initialize => 32 | .outerTest => 9 | .initializeRow => 8 | .innerTest => 9
  | .matchTest => 23 | .skip => 3 | .matched => 27 | .innerTail => 11 | .outerTail => 22

def paddingOp : PackingOp := .base (.base (.constant .value 0))
def chunkLead (start : Nat) (chunk : Chunk) : List PackingOp := (chunkCode start chunk).take (chunkLength chunk - 1)
def chunkLast (start : Nat) (chunk : Chunk) : PackingOp := (chunkCode start chunk).getD (chunkLength chunk - 1) paddingOp

theorem chunk_code_length (start : Nat) (chunk : Chunk) :
    (chunkCode start chunk).length = chunkLength chunk := by cases chunk <;> rfl

theorem chunk_span (chunk : Chunk) : chunkOffset chunk + chunkLength chunk ≤ 144 := by
  cases chunk <;> decide

theorem chunk_lead_length (start : Nat) (chunk : Chunk) :
    (chunkLead start chunk).length + 1 = chunkLength chunk := by cases chunk <;> rfl

theorem chunk_split (start : Nat) (chunk : Chunk) :
    chunkCode start chunk = chunkLead start chunk ++ [chunkLast start chunk] := by cases chunk <;> rfl

theorem chunk_slice (start : Nat) (chunk : Chunk) (position : Nat) (hp : position < chunkLength chunk) :
    (programAt start).getD (chunkOffset chunk + position) paddingOp =
      (chunkCode start chunk).getD position paddingOp := by
  cases chunk <;> dsimp only [chunkLength] at hp <;> interval_cases position <;> rfl

theorem chunk_lead_noJump (start : Nat) (chunk : Chunk) : ∀ op ∈ chunkLead start chunk, NoJump op := by
  cases chunk <;> simp [chunkLead, chunkCode, chunkLength, initializeCache, initializeRow,
    boundedTest, matchTest, matchLead, loadParent, matched, writeChild, innerTail, innerLead,
    outerTail, outerLead, writeDegree, loadRel, storeRel, setRel, incrementRel, jumpTo, NoJump]

def CodeAt (containing : List PackingOp) (start : Nat) : Prop :=
  start + 144 ≤ containing.length ∧ ∀ position < 144,
    containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp

theorem append_code (left right : List PackingOp) : CodeAt (left ++ programAt left.length ++ right) left.length := by
  constructor
  · simp only [List.length_append, programAt_length]
    omega
  · intro position hp
    rw [List.getD_append (left ++ programAt left.length) right paddingOp _
      (by simp only [List.length_append, programAt_length]; omega),
      List.getD_append_right left (programAt left.length) paddingOp _ (by omega), Nat.add_sub_cancel_left]

/-- Actual fetched prefix of every concrete block, including its final
conditional jump. This statement is used for execution, not as a premise. -/
theorem chunk_run_prefix (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : CodeAt containing start) (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    natRun rom containing count state = runOps rom ((chunkCode start chunk).take count) state := by
  rw [chunk_split start chunk]
  refine natRun_segment_prefix rom containing (chunkLead start chunk) (chunkLast start chunk)
    (start + chunkOffset chunk)
    (by have hs := chunk_span chunk; have hl := chunk_lead_length start chunk; have hb := code.1; omega)
    ?_ ?_ (chunk_lead_noJump start chunk) state hpc ha count
    (by have hl := chunk_lead_length start chunk; omega)
  · intro position hp
    have hlen := chunk_lead_length start chunk
    have hpos : position < chunkLength chunk := by omega
    have hh := (code.2 (chunkOffset chunk + position) (by have hs := chunk_span chunk; omega)).trans
      (chunk_slice start chunk position hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := chunk_span chunk; have hb := code.1; omega),
      List.getD_eq_getElem _ _ (by rw [chunk_code_length]; exact hpos)] at hh
    simpa only [Nat.add_assoc, chunkLead, List.getElem_take] using hh
  · have hlen := chunk_lead_length start chunk
    have hpos : (chunkLead start chunk).length < chunkLength chunk := by omega
    have hh := (code.2 (chunkOffset chunk + (chunkLead start chunk).length)
      (by have hs := chunk_span chunk; omega)).trans (chunk_slice start chunk _ hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := chunk_span chunk; have hb := code.1; omega)] at hh
    have heq : (chunkLead start chunk).length = chunkLength chunk - 1 := by omega
    simpa only [Nat.add_assoc, heq, chunkLast] using hh

theorem chunk_run (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
    (code : CodeAt containing start) (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false) :
    natRun rom containing (chunkLength chunk) state = runOps rom (chunkCode start chunk) state := by
  rw [chunk_run_prefix rom containing start code chunk state hpc ha _ le_rfl,
    List.take_of_length_le (by rw [chunk_code_length])]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
