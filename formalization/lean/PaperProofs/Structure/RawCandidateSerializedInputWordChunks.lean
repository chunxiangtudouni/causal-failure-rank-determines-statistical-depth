module

public import PaperProofs.Structure.RawCandidateSerializedInputRAM
public import PaperProofs.Structure.RawCandidateIncidenceWord
public import PaperProofs.Structure.RawCandidateOrderingWord

/-! Exact body slices and fetched prefixes of the original 443-op input
serializer.  Cache-base recovery remains the original twelve instructions;
there is no persistent pointer assumption on mutable output cell eight. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordChunks

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateSerializedInputRAM
open RawCandidateWorkspaceBounds (workspaceLimit)
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateOrderingWord (MacroSafe)

inductive Chunk where
  | headers | rawInit | rawTest | rawBody | nodeInit | nodeTest | toolInit | toolTest | arguments | toolTail | rowTail

def chunkCode (start : Nat) : Chunk → List PackingOp
  | .headers => headers
  | .rawInit => setCache 1 0
  | .rawTest => rawTest (start + 184)
  | .rawBody => rawBody start
  | .nodeInit => setCache 1 0
  | .nodeTest => boundedTest 1 5 (start + 443)
  | .toolInit => setCache 2 0
  | .toolTest => boundedTest 2 4 (start + 408)
  | .arguments => arguments
  | .toolTail => toolTail start
  | .rowTail => rowTail start

def chunkOffset : Chunk → Nat
  | .headers => 0 | .rawInit => 79 | .rawTest => 95 | .rawBody => 128
  | .nodeInit => 184 | .nodeTest => 200 | .toolInit => 220 | .toolTest => 236
  | .arguments => 256 | .toolTail => 337 | .rowTail => 408

def chunkLength : Chunk → Nat
  | .headers => 79 | .rawInit => 16 | .rawTest => 33 | .rawBody => 56
  | .nodeInit => 16 | .nodeTest => 20 | .toolInit => 16 | .toolTest => 20
  | .arguments => 49 | .toolTail => 71 | .rowTail => 35

def chunkNumber : Chunk → Nat
  | .headers => 0 | .rawInit => 1 | .rawTest => 2 | .rawBody => 3 | .nodeInit => 4 | .nodeTest => 5
  | .toolInit => 6 | .toolTest => 7 | .arguments => 8 | .toolTail => 10 | .rowTail => 11

def blocks (start : Nat) : List (List PackingOp) :=
  [headers, setCache 1 0, rawTest (start + 184), rawBody start, setCache 1 0,
    boundedTest 1 5 (start + 443), setCache 2 0, boundedTest 2 4 (start + 408), arguments,
    RawCandidateIncidenceBlock.programAt (start + 305), toolTail start, rowTail start]

def chunkPrefix (start : Nat) (chunk : Chunk) : List PackingOp := ((blocks start).take (chunkNumber chunk)).flatten
def chunkSuffix (start : Nat) (chunk : Chunk) : List PackingOp := ((blocks start).drop (chunkNumber chunk + 1)).flatten

theorem chunk_code_length (start : Nat) (chunk : Chunk) : (chunkCode start chunk).length = chunkLength chunk := by
  cases chunk <;>
    simp only [chunkCode, chunkLength, headers_length, setCache_length, rawTest_length, rawBody_length,
      boundedTest_length, arguments_length, toolTail_length, rowTail_length]

theorem chunk_prefix_length (start : Nat) (chunk : Chunk) : (chunkPrefix start chunk).length = chunkOffset chunk := by
  cases chunk <;>
    simp only [chunkPrefix, blocks, chunkNumber, chunkOffset, List.take, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.length_append, List.length_nil, headers_length, setCache_length, rawTest_length,
      rawBody_length, boundedTest_length, arguments_length, RawCandidateIncidenceBlock.programAt_length, toolTail_length]

theorem chunk_span (chunk : Chunk) : chunkOffset chunk + chunkLength chunk ≤ 443 := by cases chunk <;> decide

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
    simp [chunkLead, chunkCode, chunkLength, headers, loadNodeCount, readOrd, loadCache, storeCache, setCache,
      rawTest, rawBody, boundedTest, arguments, writeNode, toolTail, rowTail, incrementCache,
      RawCandidateWorkspaceBaseRAM.program, loadCell, storeCell, jumpTo, NoJump]

theorem chunk_split (start : Nat) (chunk : Chunk) : chunkCode start chunk = chunkLead start chunk ++ [chunkLast start chunk] := by
  have hpos : 0 < chunkLength chunk := by cases chunk <;> decide
  have hlast : chunkLength chunk - 1 < (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [chunkLast, List.getD_eq_getElem _ paddingOp hlast, chunkLead, ← List.take_succ_eq_append_getElem hlast]
  have heq : chunkLength chunk - 1 + 1 = (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [heq, List.take_length]

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 16 full.length q) state ∧
    ∃ offset < 443, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (h : SafePoint q full containing start state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) : Fits (indexWidth 16 full.length q) state.pc := by
  obtain ⟨offset, hoff, hp, _⟩ := h.2
  rw [hp]
  exact lt_of_le_of_lt (by omega) hend

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 443 ≤ containing.length)
  (hcode : ∀ position < 443, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

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

theorem kernel_slice : start + 305 + 32 ≤ containing.length ∧
    ∀ position < 32, containing.getD ((start + 305) + position) paddingOp =
      (RawCandidateIncidenceBlock.programAt (start + 305)).getD position paddingOp := by
  let leading := headers ++ setCache 1 0 ++ rawTest (start + 184) ++ rawBody start ++ setCache 1 0 ++
    boundedTest 1 5 (start + 443) ++ setCache 2 0 ++ boundedTest 2 4 (start + 408) ++ arguments
  have hl : leading.length = 305 := by
    simp only [leading, List.length_append, headers_length, setCache_length, rawTest_length,
      rawBody_length, boundedTest_length, arguments_length]
  have layout : programAt start = leading ++ RawCandidateIncidenceBlock.programAt (start + 305) ++
      (toolTail start ++ rowTail start) := by simp only [programAt, leading, List.append_assoc]
  refine ⟨by omega, ?_⟩
  intro position hp
  have hh := hcode (305 + position) (by omega)
  have hm : (programAt start).getD (305 + position) paddingOp =
      (RawCandidateIncidenceBlock.programAt (start + 305)).getD position paddingOp := by
    rw [layout]
    rw [List.getD_append (leading ++ RawCandidateIncidenceBlock.programAt (start + 305)) (toolTail start ++ rowTail start)
        paddingOp _ (by simp only [List.length_append, RawCandidateIncidenceBlock.programAt_length]; omega),
      List.getD_append_right leading (RawCandidateIncidenceBlock.programAt (start + 305)) paddingOp _ (by omega),
      hl, Nat.add_sub_cancel_left]
  simpa only [Nat.add_assoc] using hh.trans hm

theorem kernel_safe (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + 305)) (ha : state.halted = false)
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 443))) :
    let count := RawCandidateIncidenceWord.steps full.length candidate.val tool.val
    let result := natRun (rawIncidenceROM q full) containing count state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state count ∧
      RegistersFit (indexWidth 16 full.length q) result ∧
      RawCandidateIncidenceBlock.ReturnedActive (start + 305) state result
        (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  have slice := kernel_slice containing start hbound hcode
  have he : Fits (indexWidth 16 full.length q) (5 * ((start + 305) + 32)) := lt_of_le_of_lt (by omega) hend
  have hn := RawCandidateSerializedInputRAM.query_call q full containing start hbound hcode candidate tool state hpc ha hcandidate htool
  have endFit := RawCandidateIncidenceWord.natRun_prefix_safe q full containing (start + 305) slice.1 slice.2
    candidate tool state hpc ha hcandidate htool hf he (RawCandidateIncidenceWord.steps full.length candidate.val tool.val) le_rfl
  refine ⟨?_, endFit.1, hn⟩
  intro count hc
  have pc := RawCandidateIncidenceWord.natRun_prefix_pc q full containing (start + 305) slice.1 slice.2
    candidate tool state hpc ha hcandidate htool count hc.le
  have fit := RawCandidateIncidenceWord.natRun_prefix_safe q full containing (start + 305) slice.1 slice.2
    candidate tool state hpc ha hcandidate htool hf he count hc.le
  let index := (RawCandidateIncidenceWord.pathIndices full.length candidate.val tool.val).getD count 32
  have hi : index < 32 := RawCandidateIncidenceWord.path_index_lt _ _ _ _ hc
  let op := (RawCandidateIncidenceWord.pathOps (start + 305) full.length candidate.val tool.val).getD count paddingOp
  refine ⟨fit.1, 305 + index, by omega, ?_, fit.2.2, op, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using pc
  · rw [pc]
    change PackingOp.decode (natFetch containing (5 * ((start + 305) + index))) = some op
    rw [natFetch_body containing ((start + 305) + index) (by omega), decode_encode]
    have hh := (slice.2 index hi).trans (RawCandidateIncidenceWord.path_op_matches (start + 305) full.length candidate.val tool.val count hc)
    rw [List.getD_eq_getElem containing paddingOp (by omega)] at hh
    exact congrArg some hh
  · rw [RawCandidateIncidenceWord.natRun_prefix_eq q full containing (start + 305) slice.1 slice.2
      candidate tool state hpc ha hcandidate htool count hc.le]
    exact RawCandidateIncidenceWord.path_prefix_accessFits q full (start + 305) (workspaceLimit full.length q)
      candidate tool state hcandidate htool count hc

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateSerializedInputWordChunks
