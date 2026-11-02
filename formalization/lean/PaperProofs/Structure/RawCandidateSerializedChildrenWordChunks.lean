module

public import PaperProofs.Structure.RawCandidateSerializedChildrenRun
public import PaperProofs.Structure.RawCandidateSerializedInputWordCache
public import PaperProofs.Structure.RawCandidateOrderingWord

/-! Exact body slices and fetched prefixes of the original 427-op children
serializer.  Cache-base recovery remains the original twelve instructions;
there is no persistent pointer assumption on mutable output cell eight. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWordChunks

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateSerializedChildrenRAM
open RawCandidateWorkspaceBounds (workspaceLimit)
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateOrderingWord (MacroSafe)

open RawCandidateSerializedInputRAM (setCache loadCache storeCache incrementCache boundedTest boundedTest_length)

inductive Chunk where
  | initBlock | outerTest | initRow | innerTest | matchTest | skipMatch | matched | innerTail | outerTail

def chunkCode (start : Nat) : Chunk → List PackingOp
  | .initBlock => initBlock
  | .outerTest => boundedTest 1 5 (start + 427)
  | .initRow => initRow
  | .innerTest => boundedTest 2 5 (start + 353)
  | .matchTest => matchTest start
  | .skipMatch => jumpTo (start + 318)
  | .matched => matched
  | .innerTail => innerTail start
  | .outerTail => outerTail start

def chunkOffset : Chunk → Nat
  | .initBlock => 0 | .outerTest => 35 | .initRow => 55 | .innerTest => 127
  | .matchTest => 147 | .skipMatch => 203 | .matched => 206 | .innerTail => 318 | .outerTail => 353

def chunkLength : Chunk → Nat
  | .initBlock => 35 | .outerTest => 20 | .initRow => 72 | .innerTest => 20
  | .matchTest => 56 | .skipMatch => 3 | .matched => 112 | .innerTail => 35 | .outerTail => 74

def chunkNumber : Chunk → Nat
  | .initBlock => 0 | .outerTest => 1 | .initRow => 2 | .innerTest => 3 | .matchTest => 4
  | .skipMatch => 5 | .matched => 6 | .innerTail => 7 | .outerTail => 8

def blocks (start : Nat) : List (List PackingOp) :=
  [initBlock, boundedTest 1 5 (start + 427), initRow, boundedTest 2 5 (start + 353),
    matchTest start, jumpTo (start + 318), matched, innerTail start, outerTail start]

def chunkPrefix (start : Nat) (chunk : Chunk) : List PackingOp := ((blocks start).take (chunkNumber chunk)).flatten

def chunkSuffix (start : Nat) (chunk : Chunk) : List PackingOp := ((blocks start).drop (chunkNumber chunk + 1)).flatten

theorem chunk_code_length (start : Nat) (chunk : Chunk) : (chunkCode start chunk).length = chunkLength chunk := by
  cases chunk <;>
    simp only [chunkCode, chunkLength, initBlock_length, boundedTest_length, initRow_length,
      matchTest_length, matched_length, innerTail_length, outerTail_length, jumpTo, List.length_cons, List.length_nil]

theorem chunk_prefix_length (start : Nat) (chunk : Chunk) : (chunkPrefix start chunk).length = chunkOffset chunk := by
  cases chunk <;>
    simp only [chunkPrefix, blocks, chunkNumber, chunkOffset, List.take, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.length_append, List.length_nil, initBlock_length, boundedTest_length,
      initRow_length, matchTest_length, matched_length, innerTail_length, jumpTo, List.length_cons]

theorem chunk_span (chunk : Chunk) : chunkOffset chunk + chunkLength chunk ≤ 427 := by cases chunk <;> decide

theorem chunk_assembly (start : Nat) (chunk : Chunk) :
    programAt start = chunkPrefix start chunk ++ chunkCode start chunk ++ chunkSuffix start chunk := by
  cases chunk <;>
    simp only [programAt, chunkPrefix, chunkSuffix, chunkCode, blocks, chunkNumber, List.take, List.drop,
      List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil, List.append_assoc]

theorem chunk_slice (start : Nat) (chunk : Chunk) (position : Nat) (hp : position < chunkLength chunk) :
    (programAt start).getD (chunkOffset chunk + position) paddingOp = (chunkCode start chunk).getD position paddingOp := by
  rw [chunk_assembly start chunk, ← chunk_prefix_length start chunk]
  rw [List.getD_append (chunkPrefix start chunk ++ chunkCode start chunk) (chunkSuffix start chunk) paddingOp _
      (by rw [List.length_append, chunk_code_length]; omega),
    List.getD_append_right (chunkPrefix start chunk) (chunkCode start chunk) paddingOp _ (by omega), Nat.add_sub_cancel_left]

def chunkLead (start : Nat) (chunk : Chunk) : List PackingOp := (chunkCode start chunk).take (chunkLength chunk - 1)
def chunkLast (start : Nat) (chunk : Chunk) : PackingOp := (chunkCode start chunk).getD (chunkLength chunk - 1) paddingOp

theorem chunk_lead_length (start : Nat) (chunk : Chunk) : (chunkLead start chunk).length + 1 = chunkLength chunk := by
  rw [chunkLead, List.length_take, chunk_code_length]
  cases chunk <;> decide

theorem chunk_lead_noJump (start : Nat) (chunk : Chunk) : ∀ op ∈ chunkLead start chunk, NoJump op := by
  cases chunk <;>
    simp [chunkLead, chunkCode, chunkLength, initBlock, initRow, loadParent, loadFlat, storeFlat,
      setFlat, incrementFlat, writeParent, matchTest, matchLead, matched, writeChild, innerTail, innerLead,
      outerTail, outerLead, writeDegree, setCache, loadCache, storeCache, incrementCache, boundedTest,
      RawCandidateWorkspaceBaseRAM.program, loadCell, jumpTo, NoJump]

theorem chunk_split (start : Nat) (chunk : Chunk) : chunkCode start chunk = chunkLead start chunk ++ [chunkLast start chunk] := by
  have hpos : 0 < chunkLength chunk := by cases chunk <;> decide
  have hlast : chunkLength chunk - 1 < (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [chunkLast, List.getD_eq_getElem _ paddingOp hlast, chunkLead, ← List.take_succ_eq_append_getElem hlast]
  have heq : chunkLength chunk - 1 + 1 = (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [heq, List.take_length]

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 16 full.length q) state ∧
    ∃ offset < 427, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (h : SafePoint q full containing start state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 427))) : Fits (indexWidth 16 full.length q) state.pc := by
  obtain ⟨offset, hoff, hp, _⟩ := h.2
  rw [hp]
  exact lt_of_le_of_lt (by omega) hend

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 427 ≤ containing.length)
  (hcode : ∀ position < 427, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem chunk_run_prefix (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    natRun (rawIncidenceROM q full) containing count state = runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state := by
  rw [chunk_split start chunk]
  refine RawIncidenceScanSafety.natRun_segment_prefix (rawIncidenceROM q full) containing
    (chunkLead start chunk) (chunkLast start chunk) (start + chunkOffset chunk)
    (by have hs := chunk_span chunk; have hl := chunk_lead_length start chunk; omega)
    ?_ ?_ (chunk_lead_noJump start chunk) state hpc ha count
    (by have hl := chunk_lead_length start chunk; omega)
  · intro position hp
    have hlen := chunk_lead_length start chunk
    have hpos : position < chunkLength chunk := by omega
    have hh := (hcode (chunkOffset chunk + position) (by have hs := chunk_span chunk; omega)).trans (chunk_slice start chunk position hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := chunk_span chunk; omega),
      List.getD_eq_getElem _ _ (by rw [chunk_code_length]; exact hpos)] at hh
    simpa only [Nat.add_assoc, chunkLead, List.getElem_take] using hh
  · have hlen := chunk_lead_length start chunk
    have hpos : (chunkLead start chunk).length < chunkLength chunk := by omega
    have hh := (hcode (chunkOffset chunk + (chunkLead start chunk).length) (by have hs := chunk_span chunk; omega)).trans
      (chunk_slice start chunk _ hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := chunk_span chunk; omega)] at hh
    have heq : (chunkLead start chunk).length = chunkLength chunk - 1 := by omega
    simpa only [Nat.add_assoc, heq, chunkLast] using hh

theorem chunk_run (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing (chunkLength chunk) state = runOps (rawIncidenceROM q full) (chunkCode start chunk) state := by
  rw [chunk_run_prefix q full containing start hbound hcode chunk state hpc ha _ le_rfl,
    List.take_of_length_le (by rw [chunk_code_length])]

theorem chunk_of_macro (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hm : MacroSafe q full (chunkCode start chunk) state) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  constructor
  · intro count hc
    have hr := chunk_run_prefix q full containing start hbound hcode chunk state hpc ha count hc.le
    have hsmall : count ≤ chunkLength chunk - 1 := by omega
    have heq : (chunkCode start chunk).take count = (chunkLead start chunk).take count := by rw [chunkLead, List.take_take, min_eq_left hsmall]
    have hno : ∀ op ∈ (chunkCode start chunk).take count, NoJump op := by
      rw [heq]
      exact fun op hop => chunk_lead_noJump start chunk op (List.mem_of_mem_take hop)
    have hp : (natRun (rawIncidenceROM q full) containing count state).pc = 5 * (start + chunkOffset chunk + count) := by
      rw [hr, runOps_pc _ _ _ hno, List.length_take_of_le (by rw [chunk_code_length]; omega), hpc]
      omega
    have hs := chunk_span chunk
    refine ⟨?_, chunkOffset chunk + count, by omega, ?_, ?_, (chunkCode start chunk).getD count paddingOp, ?_, ?_⟩
    · rw [hr]
      exact hm.1 count (by rw [chunk_code_length]; exact hc.le)
    · rw [hp]; omega
    · rw [hr, runOps_halted, ha]
    · rw [hp, natFetch_body containing (start + chunkOffset chunk + count) (by omega), decode_encode]
      have hh := (hcode (chunkOffset chunk + count) (by omega)).trans (chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ paddingOp (by omega)] at hh
      simpa only [Nat.add_assoc] using congrArg some hh
    · rw [hr]
      exact hm.2 count (by rw [chunk_code_length]; exact hc)
  · rw [chunk_run q full containing start hbound hcode chunk state hpc ha]
    exact hm.full

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedChildrenWordChunks
