module

public import PaperProofs.Structure.RawCandidatePairScan
public import PaperProofs.Structure.RawCandidateIncidenceWord
public import PaperProofs.Structure.RawCandidateWorkspaceBounds
import Mathlib.Tactic.IntervalCases

/-! Word safety of the existing dynamic q-pair loop.  Its initialization
overwrites the unknown q/counter scratch cells; only candidate IDs are
caller data.  No list of q iterations is compiled into the program. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidatePairScanWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine
  RawIncidenceLaminarRAM RawIncidenceScanSafety RawCandidateWorkspaceBounds
open RawCandidatePairScan (programAt initBlock leftArguments rightArguments updateLead update)

def paddingOp : PackingOp := .base (.base (.constant .value 0))

inductive Chunk where
  | init | test | leftArgs | rightArgs | update

def chunkCode (start : Nat) : Chunk → List PackingOp
  | .init => initBlock
  | .test => testCell 0 3 (start + 125)
  | .leftArgs => leftArguments
  | .rightArgs => rightArguments
  | .update => update start

def chunkOffset : Chunk → Nat
  | .init => 0 | .test => 16 | .leftArgs => 23 | .rightArgs => 59 | .update => 97

def chunkLength : Chunk → Nat
  | .init => 16 | .test => 7 | .leftArgs => 4 | .rightArgs => 6 | .update => 28

def chunkLead (start : Nat) (chunk : Chunk) : List PackingOp :=
  (chunkCode start chunk).take (chunkLength chunk - 1)

def chunkLast (start : Nat) (chunk : Chunk) : PackingOp :=
  (chunkCode start chunk).getD (chunkLength chunk - 1) paddingOp

theorem chunk_length (start : Nat) (chunk : Chunk) : (chunkCode start chunk).length = chunkLength chunk := by
  cases chunk <;> rfl

theorem chunk_span (chunk : Chunk) : chunkOffset chunk + chunkLength chunk ≤ 125 := by cases chunk <;> decide

theorem chunk_split (start : Nat) (chunk : Chunk) :
    chunkCode start chunk = chunkLead start chunk ++ [chunkLast start chunk] := by cases chunk <;> rfl

theorem chunk_lead_length (start : Nat) (chunk : Chunk) : (chunkLead start chunk).length + 1 = chunkLength chunk := by
  have h := congrArg List.length (chunk_split start chunk)
  simp only [chunk_length, List.length_append, List.length_cons, List.length_nil] at h
  omega

theorem chunk_lead_noJump (start : Nat) (chunk : Chunk) : ∀ op ∈ chunkLead start chunk, NoJump op := by
  cases chunk <;>
    dsimp [chunkLead, chunkCode, chunkLength, initBlock, testCell, leftArguments, rightArguments,
      update, updateLead, setCell, loadCell, storeCell, addWitness, incrementCell, jumpTo, NoJump]
  all_goals simp

theorem chunk_matches (start : Nat) (chunk : Chunk) (position : Nat) (hp : position < chunkLength chunk) :
    (programAt start).getD (chunkOffset chunk + position) paddingOp = (chunkCode start chunk).getD position paddingOp := by
  cases chunk
  · change position < 16 at hp
    interval_cases position <;> rfl
  · change position < 7 at hp
    interval_cases position <;> rfl
  · change position < 4 at hp
    interval_cases position <;> rfl
  · change position < 6 at hp
    interval_cases position <;> rfl
  · change position < 28 at hp
    interval_cases position <;> rfl

private theorem small_fits (N q value : Nat) (hv : value ≤ N * q + N + q + 640) : Fits (indexWidth 16 N q) value :=
  hv.trans_lt (fits_checker_register_bound N q)

theorem init_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (count : Nat) (hc : count ≤ 16) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (initBlock.take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [initBlock, setCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_q]
  all_goals first | exact hf _ | apply small_fits; omega

theorem test_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (h0 : state.heap 0 ≤ q) (h3 : state.heap 3 ≤ q)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ 7) :
    RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((testCell 0 3 (start + 125)).take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [testCell, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | exact hend | apply small_fits; omega

theorem leftArgs_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (h1 : state.heap 1 < full.length + q + 1) (h3 : state.heap 3 ≤ q)
    (count : Nat) (hc : count ≤ 4) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (leftArguments.take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | apply small_fits; omega

theorem rightArgs_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (h2 : state.heap 2 < full.length + q + 1) (h3 : state.heap 3 ≤ q)
    (count : Nat) (hc : count ≤ 6) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) (rightArguments.take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [rightArguments, storeCell, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | apply small_fits; omega

theorem update_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (h3 : state.heap 3 < q) (h4 : state.heap 4 ≤ state.heap 3)
    (h5 : state.heap 5 ≤ state.heap 3) (h6 : state.heap 6 ≤ state.heap 3)
    (h7 : state.heap 7 ≤ 1) (hvalue : state.register .value ≤ 1)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ 28) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) ((update start).take count) state) := by
  have hloop : Fits (indexWidth 16 full.length q) (5 * (start + 16)) := lt_of_le_of_lt (by omega) hend
  have hmin : min (state.heap 7) (state.register .value) ≤ 1 := (Nat.min_le_left _ _).trans h7
  have hleft : state.heap 7 - state.register .value ≤ 1 := (Nat.sub_le _ _).trans h7
  have hright : state.register .value - state.heap 7 ≤ 1 := (Nat.sub_le _ _).trans hvalue
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [update, updateLead, loadCell, addWitness, incrementCell, storeCell, jumpTo,
      runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | exact hloop | apply small_fits; omega

theorem chunk_prefix_accessFits (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (chunk : Chunk)
    (state : NatState) (count : Nat) (hc : count < chunkLength chunk) :
    NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)
      ((chunkCode start chunk).getD count paddingOp) := by
  have hw : 8 ≤ workspaceLimit full.length q := by
    have hb := RawCandidateWorkspaceInit.workspaceBase_ge full.length q
    unfold workspaceLimit
    omega
  cases chunk
  all_goals dsimp only [chunkLength] at hc
  all_goals interval_cases count
  all_goals
    simp [chunkCode, initBlock, testCell, leftArguments, rightArguments, update, updateLead,
      setCell, storeCell, loadCell, addWitness, incrementCell, jumpTo, runOps, natExecuteOp,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]
  all_goals omega

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 16 full.length q) state ∧
    ∃ offset < 125, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (h : SafePoint q full containing start state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125))) :
    Fits (indexWidth 16 full.length q) state.pc := by
  rcases h.2 with ⟨offset, hoff, hp, _⟩
  rw [hp]
  exact lt_of_le_of_lt (by omega) hend

theorem candidateBit_le_one {q : Nat} (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) (column : Nat) : RawCandidatePairScan.candidateBit full candidate column ≤ 1 := by
  unfold RawCandidatePairScan.candidateBit
  split
  · unfold bit
    split <;> omega
  · omega

private theorem sum_le_count (f : Nat → Nat) (hf : ∀ column, f column ≤ 1) (count : Nat) :
    (∑ column ∈ Finset.range count, f column) ≤ count := by
  calc
    _ ≤ ∑ _column ∈ Finset.range count, 1 := Finset.sum_le_sum (fun column _ => hf column)
    _ = _ := by simp

theorem witness_sums_le {q : Nat} (full : List (Finset (Fin q)))
    (left right : Fin (full.length + q + 1)) (count : Nat) :
    (∑ column ∈ Finset.range count, min (RawCandidatePairScan.candidateBit full left column)
      (RawCandidatePairScan.candidateBit full right column)) ≤ count ∧
    (∑ column ∈ Finset.range count, (RawCandidatePairScan.candidateBit full left column -
      RawCandidatePairScan.candidateBit full right column)) ≤ count ∧
    (∑ column ∈ Finset.range count, (RawCandidatePairScan.candidateBit full right column -
      RawCandidatePairScan.candidateBit full left column)) ≤ count := by
  refine ⟨sum_le_count _ (fun column => (Nat.min_le_left _ _).trans (candidateBit_le_one full left column)) count,
    sum_le_count _ (fun column => (Nat.sub_le _ _).trans (candidateBit_le_one full left column)) count,
    sum_le_count _ (fun column => (Nat.sub_le _ _).trans (candidateBit_le_one full right column)) count⟩

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 125 ≤ containing.length)
  (hcode : ∀ position < 125, containing.getD (start + position) paddingOp =
    (programAt start).getD position paddingOp)

include hbound hcode

theorem chunk_slice (chunk : Chunk) :
    start + chunkOffset chunk + chunkLength chunk ≤ containing.length ∧
      ∀ position < chunkLength chunk, containing.getD ((start + chunkOffset chunk) + position) paddingOp =
        (chunkCode start chunk).getD position paddingOp := by
  have hspan := chunk_span chunk
  refine ⟨by omega, ?_⟩
  intro position hp
  have hh := (hcode (chunkOffset chunk + position) (by omega)).trans (chunk_matches start chunk position hp)
  simpa only [Nat.add_assoc] using hh

theorem chunk_run_prefix (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    natRun (rawIncidenceROM q full) containing count state =
      runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state := by
  have hs := chunk_slice containing start hbound hcode chunk
  have hlen := chunk_lead_length start chunk
  rw [chunk_split start chunk]
  apply natRun_segment_prefix (rawIncidenceROM q full) containing (chunkLead start chunk)
    (chunkLast start chunk) (start + chunkOffset chunk) (by omega) ?_ ?_
    (chunk_lead_noJump start chunk) state hpc ha count (by omega)
  · intro position hp
    have hh := hs.2 position (by omega)
    rw [chunk_split start chunk, List.getD_append _ _ _ _ hp,
      List.getD_eq_getElem _ paddingOp (by omega), List.getD_eq_getElem _ paddingOp hp] at hh
    exact hh
  · have hh := hs.2 (chunkLead start chunk).length (by omega)
    rw [chunk_split start chunk, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
      List.getD_cons_zero, List.getD_eq_getElem _ paddingOp (by omega)] at hh
    exact hh

theorem chunk_run (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing (chunkLength chunk) state =
      runOps (rawIncidenceROM q full) (chunkCode start chunk) state := by
  rw [chunk_run_prefix q full containing start hbound hcode chunk state hpc ha _ le_rfl,
    List.take_of_length_le (by rw [chunk_length])]

omit hbound hcode in
private theorem chunk_pure_prefix_pc (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk))
    (count : Nat) (hc : count < chunkLength chunk) :
    (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state).pc =
      5 * (start + (chunkOffset chunk + count)) := by
  have hlen := chunk_lead_length start chunk
  have hc' : count ≤ (chunkLead start chunk).length := by omega
  rw [chunk_split start chunk, List.take_append_of_le_length hc',
    runOps_pc _ _ _ (fun op hop => chunk_lead_noJump start chunk op (List.mem_of_mem_take hop)),
    List.length_take_of_le hc', hpc]
  omega

theorem chunk_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hregs : ∀ count ≤ chunkLength chunk,
      RegistersFit (indexWidth 16 full.length q)
        (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  refine ⟨?_, ?_⟩
  · intro count hc
    rw [chunk_run_prefix q full containing start hbound hcode chunk state hpc ha count hc.le]
    have hspan := chunk_span chunk
    have hs := chunk_slice containing start hbound hcode chunk
    have hp := chunk_pure_prefix_pc q full start chunk state hpc count hc
    refine ⟨hregs count hc.le, chunkOffset chunk + count, by omega, hp,
      (runOps_halted _ _ _).trans ha, (chunkCode start chunk).getD count paddingOp, ?_,
      chunk_prefix_accessFits q full start chunk state count hc⟩
    rw [hp, show start + (chunkOffset chunk + count) = (start + chunkOffset chunk) + count by omega,
      natFetch_body containing ((start + chunkOffset chunk) + count) (by omega), decode_encode]
    have hh := hs.2 count hc
    rw [List.getD_eq_getElem containing paddingOp (by omega)] at hh
    exact congrArg some hh
  · rw [chunk_run_prefix q full containing start hbound hcode chunk state hpc ha _ le_rfl]
    exact hregs _ le_rfl

theorem kernel_slice (offset : Nat) (hoffset : offset = 27 ∨ offset = 65) :
    start + offset + 32 ≤ containing.length ∧
      ∀ position < 32, containing.getD ((start + offset) + position) paddingOp =
        (RawCandidateIncidenceBlock.programAt (start + offset)).getD position paddingOp := by
  have hoff : offset ≤ 65 := by rcases hoffset with rfl | rfl <;> omega
  refine ⟨by omega, ?_⟩
  intro position hp
  have hh := hcode (offset + position) (by omega)
  have hl : (programAt start).getD (offset + position) paddingOp =
      (RawCandidateIncidenceBlock.programAt (start + offset)).getD position paddingOp := by
    rcases hoffset with rfl | rfl <;> interval_cases position <;> rfl
  simpa only [Nat.add_assoc] using hh.trans hl

theorem kernel_safe (offset : Nat) (hoffset : offset = 27 ∨ offset = 65)
    (candidate : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + offset)) (ha : state.halted = false)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (hcandidate : state.register .old = candidate.val) (htool : state.register .fresh = tool.val) :
    let count := RawCandidateIncidenceWord.steps full.length candidate.val tool.val
    let result := natRun (rawIncidenceROM q full) containing count state
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state count ∧
      RegistersFit (indexWidth 16 full.length q) result ∧
      RawCandidateIncidenceBlock.ReturnedActive (start + offset) state result
        (bit (decide (tool ∈ (RawCandidateOrder.candidateSupports q full).getD candidate.val ∅))) := by
  have hoff : offset ≤ 65 := by rcases hoffset with rfl | rfl <;> omega
  have hs := kernel_slice containing start hbound hcode offset hoffset
  have he : Fits (indexWidth 16 full.length q) (5 * ((start + offset) + 32)) := lt_of_le_of_lt (by omega) hend
  have hn := RawCandidateIncidenceBlock.query q full containing (start + offset) hs.1 (by
    intro position hp
    have hh := hs.2 position hp
    rw [List.getD_eq_getElem containing paddingOp (by omega),
      List.getD_eq_getElem _ paddingOp (by rw [RawCandidateIncidenceBlock.programAt_length]; exact hp)] at hh
    exact hh) candidate tool state hpc ha hcandidate htool
  have hf := RawCandidateIncidenceWord.natRun_prefix_safe q full containing (start + offset) hs.1 hs.2
    candidate tool state hpc ha hcandidate htool hfit he
    (RawCandidateIncidenceWord.steps full.length candidate.val tool.val) le_rfl
  refine ⟨?_, hf.1, hn⟩
  intro count hc
  have hp := RawCandidateIncidenceWord.natRun_prefix_pc q full containing (start + offset) hs.1 hs.2
    candidate tool state hpc ha hcandidate htool count hc.le
  have hf := RawCandidateIncidenceWord.natRun_prefix_safe q full containing (start + offset) hs.1 hs.2
    candidate tool state hpc ha hcandidate htool hfit he count hc.le
  let index := (RawCandidateIncidenceWord.pathIndices full.length candidate.val tool.val).getD count 32
  have hi : index < 32 := RawCandidateIncidenceWord.path_index_lt _ _ _ _ hc
  let op := (RawCandidateIncidenceWord.pathOps (start + offset) full.length candidate.val tool.val).getD count paddingOp
  refine ⟨hf.1, offset + index, by omega, ?_, hf.2.2, op, ?_, ?_⟩
  · simpa only [Nat.add_assoc] using hp
  · rw [hp]
    change PackingOp.decode (natFetch containing (5 * ((start + offset) + index))) = some op
    rw [natFetch_body containing ((start + offset) + index) (by omega), decode_encode]
    have hh := (hs.2 index hi).trans (RawCandidateIncidenceWord.path_op_matches (start + offset)
      full.length candidate.val tool.val count hc)
    rw [List.getD_eq_getElem containing paddingOp (by omega)] at hh
    exact congrArg some hh
  · rw [RawCandidateIncidenceWord.natRun_prefix_eq q full containing (start + offset) hs.1 hs.2
      candidate tool state hpc ha hcandidate htool count hc.le]
    exact RawCandidateIncidenceWord.path_prefix_accessFits q full (start + offset) (workspaceLimit full.length q)
      candidate tool state hcandidate htool count hc

theorem iteration_safe (left right : Fin (full.length + q + 1)) (tool : Fin q) (state : NatState)
    (hpc : state.pc = 5 * (start + 16)) (ha : state.halted = false)
    (hq : state.heap 0 = q) (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (ht : state.heap 3 = tool.val) (h4 : state.heap 4 ≤ tool.val) (h5 : state.heap 5 ≤ tool.val) (h6 : state.heap 6 ≤ tool.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125))) :
    let count := RawCandidatePairScan.iterationSteps full.length left.val right.val tool.val
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state count ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state) := by
  let rom := rawIncidenceROM q full
  let s0 := runOps rom (testCell 0 3 (start + 125)) state
  have tr := runOps_testCell rom 0 3 (start + 125) state
  have th : s0.heap = state.heap := tr.1
  have tp : s0.pc = 5 * (start + 23) := by
    have hp := tr.2.2.1
    rw [hq, ht, ite_eq_right (Nat.sub_ne_zero_of_lt tool.isLt), hpc] at hp
    dsimp only [s0]
    omega
  have ta : s0.halted = false := tr.2.2.2.trans ha
  have ts := chunk_safe q full containing start hbound hcode .test state hpc ha (by
    intro count hc
    exact test_prefix_registersFit q full start state hfit (hq.le.trans le_rfl) (by rw [ht]; exact tool.isLt.le) hend count hc)
  rw [chunk_run q full containing start hbound hcode .test state hpc ha] at ts
  let s1 := runOps rom leftArguments s0
  have p1 : s1.pc = 5 * (start + 27) := by
    rw [show s1 = runOps _ _ _ from rfl, runOps_pc _ _ _ (by simp [leftArguments, loadCell, NoJump]), tp]
    change 5 * (start + 23) + 5 * 4 = _
    omega
  have a1 : s1.halted = false := (runOps_halted _ _ _).trans ta
  have h1 : s1.heap = state.heap := by simpa [s1, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using th
  have old1 : s1.register .old = left.val := by
    simpa [s1, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, th] using hl
  have fresh1 : s1.register .fresh = tool.val := by
    simpa [s1, leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, th] using ht
  have as1 := chunk_safe q full containing start hbound hcode .leftArgs s0 tp ta (by
    intro count hc
    exact leftArgs_prefix_registersFit q full s0 ts.2 (by rw [th, hl]; exact left.isLt) (by rw [th, ht]; exact tool.isLt.le) count hc)
  rw [chunk_run q full containing start hbound hcode .leftArgs s0 tp ta] at as1
  let ls := RawCandidateIncidenceWord.steps full.length left.val tool.val
  let rs := RawCandidateIncidenceWord.steps full.length right.val tool.val
  let s2 := natRun rom containing ls s1
  have lk := kernel_safe q full containing start hbound hcode 27 (Or.inl rfl) left tool s1 p1 a1 as1.2 hend old1 fresh1
  dsimp only at lk
  have lkReturn := lk.2.2
  have hv2 : s2.register .value = RawCandidatePairScan.candidateBit full left tool.val := by
    simpa only [RawCandidatePairScan.candidateBit_fin] using lkReturn.1
  have h2 : s2.heap = state.heap := lkReturn.2.2.2.1.trans h1
  have p2 : s2.pc = 5 * (start + 59) := by have h := lkReturn.2.2.2.2.1; dsimp only [s2]; omega
  have a2 : s2.halted = false := lkReturn.2.2.2.2.2
  let s3 := runOps rom rightArguments s2
  have p3 : s3.pc = 5 * (start + 65) := by
    rw [show s3 = runOps _ _ _ from rfl, runOps_pc _ _ _ (by simp [rightArguments, loadCell, storeCell, NoJump]), p2]
    change 5 * (start + 59) + 5 * 6 = _
    omega
  have a3 : s3.halted = false := (runOps_halted _ _ _).trans a2
  have h3 : s3.heap = Function.update state.heap 7 (RawCandidatePairScan.candidateBit full left tool.val) := by
    simp [s3, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, h2, hv2]
  have old3 : s3.register .old = right.val := by
    simpa [s3, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, h2] using hr
  have fresh3 : s3.register .fresh = tool.val := by
    simpa [s3, rightArguments, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, h2] using ht
  have as3 := chunk_safe q full containing start hbound hcode .rightArgs s2 p2 a2 (by
    intro count hc
    exact rightArgs_prefix_registersFit q full s2 lk.2.1 (by rw [h2, hr]; exact right.isLt) (by rw [h2, ht]; exact tool.isLt.le) count hc)
  rw [chunk_run q full containing start hbound hcode .rightArgs s2 p2 a2] at as3
  let s4 := natRun rom containing rs s3
  have rk := kernel_safe q full containing start hbound hcode 65 (Or.inr rfl) right tool s3 p3 a3 as3.2 hend old3 fresh3
  dsimp only at rk
  have rkReturn := rk.2.2
  have hv4 : s4.register .value = RawCandidatePairScan.candidateBit full right tool.val := by
    simpa only [RawCandidatePairScan.candidateBit_fin] using rkReturn.1
  have h4heap : s4.heap = Function.update state.heap 7 (RawCandidatePairScan.candidateBit full left tool.val) := rkReturn.2.2.2.1.trans h3
  have p4 : s4.pc = 5 * (start + 97) := by have h := rkReturn.2.2.2.2.1; dsimp only [s4]; omega
  have a4 : s4.halted = false := rkReturn.2.2.2.2.2
  have hbit (candidate : Fin (full.length + q + 1)) : RawCandidatePairScan.candidateBit full candidate tool.val ≤ 1 := by
    rw [RawCandidatePairScan.candidateBit_fin]
    simp only [bit]
    split <;> omega
  have us := chunk_safe q full containing start hbound hcode .update s4 p4 a4 (by
    intro count hc
    apply update_prefix_registersFit q full start s4 rk.2.1
    · simpa only [h4heap, Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using tool.isLt
    · simpa only [h4heap, Function.update_of_ne (by decide : (4 : Nat) ≠ 7),
        Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using h4
    · simpa only [h4heap, Function.update_of_ne (by decide : (5 : Nat) ≠ 7),
        Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using h5
    · simpa only [h4heap, Function.update_of_ne (by decide : (6 : Nat) ≠ 7),
        Function.update_of_ne (by decide : (3 : Nat) ≠ 7), ht] using h6
    · simpa only [h4heap, Function.update_self] using hbit left
    · simpa only [hv4] using hbit right
    · exact hend
    · exact hc)
  have runTest : natRun (rawIncidenceROM q full) containing 7 state = s0 :=
    chunk_run q full containing start hbound hcode .test state hpc ha
  have runLeft : natRun (rawIncidenceROM q full) containing 4 s0 = s1 :=
    chunk_run q full containing start hbound hcode .leftArgs s0 tp ta
  have runRight : natRun (rawIncidenceROM q full) containing 6 s2 = s3 :=
    chunk_run q full containing start hbound hcode .rightArgs s2 p2 a2
  have sp4 : PrefixSafe (SafePoint q full containing start) rom containing s3 (rs + 28) :=
    PrefixSafe.add _ _ _ _ rs 28 rk.1 us.1
  have sp3 : PrefixSafe (SafePoint q full containing start) rom containing s2 (6 + (rs + 28)) := by
    apply PrefixSafe.add _ _ _ _ 6 (rs + 28) as3.1
    rw [runRight]
    exact sp4
  have sp2 : PrefixSafe (SafePoint q full containing start) rom containing s1 (ls + (6 + (rs + 28))) :=
    PrefixSafe.add _ _ _ _ ls _ lk.1 sp3
  have sp1 : PrefixSafe (SafePoint q full containing start) rom containing s0 (4 + (ls + (6 + (rs + 28)))) := by
    apply PrefixSafe.add _ _ _ _ 4 _ as1.1
    rw [runLeft]
    exact sp2
  have sp0 : PrefixSafe (SafePoint q full containing start) rom containing state (7 + (4 + (ls + (6 + (rs + 28))))) := by
    apply PrefixSafe.add _ _ _ _ 7 _ ts.1
    rw [runTest]
    exact sp1
  have hsteps : RawCandidatePairScan.iterationSteps full.length left.val right.val tool.val =
      7 + (4 + (ls + (6 + (rs + 28)))) := by
    dsimp only [RawCandidatePairScan.iterationSteps, ls, rs, RawCandidateIncidenceWord.steps]
    omega
  refine ⟨by simpa only [hsteps] using sp0, ?_⟩
  rw [hsteps, natRun_add, runTest]
  change RegistersFit _ (natRun rom containing (4 + (ls + (6 + (rs + 28)))) s0)
  rw [natRun_add, runLeft, natRun_add]
  change RegistersFit _ (natRun rom containing (6 + (rs + 28)) s2)
  rw [natRun_add, runRight, natRun_add]
  exact us.2

theorem scan_partial_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * (start + 16)) (ha : state.halted = false)
    (hq : state.heap 0 = q) (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (h3 : state.heap 3 = 0) (h4 : state.heap 4 = 0) (h5 : state.heap 5 = 0) (h6 : state.heap 6 = 0)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ q) :
    let clock := RawCandidatePairScan.scanSteps full.length left.val right.val count
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state clock ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing clock state) := by
  revert hc
  induction count with
  | zero =>
    intro _
    simpa only [RawCandidatePairScan.scanSteps, Finset.range_zero, Finset.sum_empty, natRun] using
      (show PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 0 ∧
        RegistersFit (indexWidth 16 full.length q) state from ⟨by intro clock hk; omega, hfit⟩)
  | succ count ih =>
    intro hc
    rcases ih (by omega) with ⟨safe, fits⟩
    let previous := natRun (rawIncidenceROM q full) containing (RawCandidatePairScan.scanSteps full.length left.val right.val count) state
    have hs := RawCandidatePairScan.scan_partial q full containing start hbound hcode left right state hpc ha hq hl hr h3 count (by omega)
    dsimp only at hs
    rcases hs with ⟨cursor, inter, leftOnly, rightOnly, frame, pointer, active⟩
    have hq' : previous.heap 0 = q := (frame 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hq
    have hl' : previous.heap 1 = left.val := (frame 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
    have hr' : previous.heap 2 = right.val := (frame 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
    rw [h4, Nat.zero_add] at inter
    rw [h5, Nat.zero_add] at leftOnly
    rw [h6, Nat.zero_add] at rightOnly
    have hb := witness_sums_le full left right count
    have hi := iteration_safe q full containing start hbound hcode left right ⟨count, by omega⟩ previous pointer active
      hq' hl' hr' cursor (inter.le.trans hb.1) (leftOnly.le.trans hb.2.1) (rightOnly.le.trans hb.2.2) fits hend
    dsimp only at hi
    refine ⟨?_, ?_⟩
    · rw [RawCandidatePairScan.scanSteps_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe hi.1
    · rw [RawCandidatePairScan.scanSteps_succ, natRun_add]
      exact hi.2

theorem scan_nat_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125))) :
    let clock := RawCandidatePairScan.totalSteps full.length left.val right.val q
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state clock ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing clock state) := by
  let rom := rawIncidenceROM q full
  let initialized := runOps rom initBlock state
  have hip : state.pc = 5 * (start + chunkOffset .init) := by simpa only [chunkOffset, Nat.add_zero] using hpc
  have his := chunk_safe q full containing start hbound hcode .init state hip ha (by
    intro count hc
    exact init_prefix_registersFit q full state hfit count hc)
  rw [chunk_run q full containing start hbound hcode .init state hip ha] at his
  have hi : initialized.heap 0 = q ∧ initialized.heap 3 = 0 ∧ initialized.heap 4 = 0 ∧
      initialized.heap 5 = 0 ∧ initialized.heap 6 = 0 ∧
      (∀ address, address ≠ 0 → address ≠ 3 → address ≠ 4 → address ≠ 5 → address ≠ 6 →
        initialized.heap address = state.heap address) := by
    simp [initialized, initBlock, setCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, rom, raw_header_q]
    intro address h0 h3 h4 h5 h6
    simp [h0, h3, h4, h5, h6]
  have p0 : initialized.pc = 5 * (start + 16) := by
    rw [show initialized = runOps _ _ _ from rfl, runOps_pc _ _ _ (by simp [initBlock, setCell, storeCell, NoJump]), hpc]
    change 5 * start + 5 * 16 = _
    omega
  have a0 : initialized.halted = false := (runOps_halted _ _ _).trans ha
  have il : initialized.heap 1 = left.val := (hi.2.2.2.2.2 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hl
  have ir : initialized.heap 2 = right.val := (hi.2.2.2.2.2 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hr
  have ss := scan_partial_safe q full containing start hbound hcode left right initialized p0 a0 hi.1 il ir
    hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 his.2 hend q le_rfl
  let clock := RawCandidatePairScan.scanSteps full.length left.val right.val q
  let previous := natRun rom containing clock initialized
  have sem := RawCandidatePairScan.scan_partial q full containing start hbound hcode left right initialized
    p0 a0 hi.1 il ir hi.2.1 q le_rfl
  dsimp only at sem
  rcases sem with ⟨cursor, _inter, _leftOnly, _rightOnly, frame, pointer, active⟩
  have pq : previous.heap 0 = q := (frame 0 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hi.1
  have ts := chunk_safe q full containing start hbound hcode .test previous pointer active (by
    intro count hc
    exact test_prefix_registersFit q full start previous ss.2 pq.le cursor.le hend count hc)
  have ps : PrefixSafe (SafePoint q full containing start) rom containing initialized (clock + 7) :=
    PrefixSafe.add _ _ _ _ clock 7 ss.1 ts.1
  have runInit : natRun (rawIncidenceROM q full) containing 16 state = initialized :=
    chunk_run q full containing start hbound hcode .init state hip ha
  have allSafe : PrefixSafe (SafePoint q full containing start) rom containing state (16 + (clock + 7)) := by
    apply PrefixSafe.add _ _ _ _ 16 _ his.1
    rw [runInit]
    exact ps
  have hsteps : RawCandidatePairScan.totalSteps full.length left.val right.val q = 16 + (clock + 7) := by
    dsimp only [RawCandidatePairScan.totalSteps, clock]
    omega
  refine ⟨by simpa only [hsteps] using allSafe, ?_⟩
  rw [hsteps, natRun_add, runInit, natRun_add]
  exact ts.2

theorem natRun_prefix_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ RawCandidatePairScan.totalSteps full.length left.val right.val q) :
    RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state) ∧
      Fits (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing count state).pc ∧
      (natRun (rawIncidenceROM q full) containing count state).halted = false := by
  have hs := scan_nat_safe q full containing start hbound hcode left right state hpc ha hl hr hfit hend
  by_cases heq : count = RawCandidatePairScan.totalSteps full.length left.val right.val q
  · subst count
    have hn := RawCandidatePairScan.scan q full containing start hbound hcode left right state hpc ha hl hr
    dsimp only at hn
    exact ⟨hs.2, lt_of_le_of_lt hn.2.2.2.2.2.2.1.le hend, hn.2.2.2.2.2.2.2⟩
  · have hp := hs.1 count (by omega)
    rcases hp.2 with ⟨offset, hoff, hpc', active, _⟩
    exact ⟨hp.1, lt_of_le_of_lt (by rw [hpc']; omega) hend, active⟩

theorem word_run_eq_nat (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ RawCandidatePairScan.totalSteps full.length left.val right.val q) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  have hs := natRun_prefix_safe q full containing start hbound hcode left right state hpc ha hl hr hfit hend k (by omega)
  exact ⟨hs.1, hs.2.1⟩

theorem word_prefix_values (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ RawCandidatePairScan.totalSteps full.length left.val right.val q) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    (∀ register, (after.register register).toNat =
      (natRun (rawIncidenceROM q full) containing count state).register register) ∧
      after.pc.toNat = (natRun (rawIncidenceROM q full) containing count state).pc ∧ after.halted = false := by
  have hs := natRun_prefix_safe q full containing start hbound hcode left right state hpc ha hl hr hfit hend count hc
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode left right state hpc ha hl hr hfit hend hwords count hc]
  exact ⟨fun register => toWord_register_toNat _ _ hs.1 register, Nat.mod_eq_of_lt hs.2.1, hs.2.2⟩

theorem word_prefix_safe (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count < RawCandidatePairScan.totalSteps full.length left.val right.val q) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧ after.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ offset < 125, after.pc.toNat = 5 * (start + offset) ∧
        ∃ op, PackingOp.decode (fetch containing after) = some op ∧
          packingAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) after op := by
  have hp := (scan_nat_safe q full containing start hbound hcode left right state hpc ha hl hr hfit hend).1 count hc
  have hpcFit := hp.pcFits hend
  rcases hp.2 with ⟨offset, hoff, pointer, active, op, decoded, access⟩
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode left right state hpc ha hl hr hfit hend hwords count hc.le]
  have hpcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord
      (indexWidth 16 full.length q)).pc.toNat = 5 * (start + offset) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcFit, pointer]
  refine ⟨active, ?_, offset, hoff, hpcWord, op, ?_, ?_⟩
  · rw [hpcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      (BitVec.ofNat _ (natRun (rawIncidenceROM q full) containing count state).pc).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpcFit, physicalFetch_eq _ _ _ hwords]
    exact decoded
  · exact physical_access_of_nat _ (workspaceLimit full.length q) _ _ hp.1 access

structure WordScanned (N q start : Nat) (left right : Finset (Fin q))
    (before after : WordState (indexWidth 16 N q)) : Prop where
  q_cell : (after.heap (BitVec.ofNat (indexWidth 16 N q) 0)).toNat = q
  cursor : (after.heap (BitVec.ofNat (indexWidth 16 N q) 3)).toNat = q
  intersection : (after.heap (BitVec.ofNat (indexWidth 16 N q) 4)).toNat = (left ∩ right).card
  left_only : (after.heap (BitVec.ofNat (indexWidth 16 N q) 5)).toNat = (left \ right).card
  right_only : (after.heap (BitVec.ofNat (indexWidth 16 N q) 6)).toNat = (right \ left).card
  heap_frame : ∀ address, address.toNat ≠ 0 → address.toNat ≠ 3 → address.toNat ≠ 4 →
    address.toNat ≠ 5 → address.toNat ≠ 6 → address.toNat ≠ 7 → after.heap address = before.heap address
  pc : after.pc.toNat = 5 * (start + 125)
  active : after.halted = false

theorem scan_word (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 125)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    WordScanned full.length q start ((RawCandidateOrder.candidateSupports q full).getD left.val ∅)
      ((RawCandidateOrder.candidateSupports q full).getD right.val ∅) (state.toWord (indexWidth 16 full.length q))
      (packingRun (rawIncidenceROM q full) containing (RawCandidatePairScan.totalSteps full.length left.val right.val q)
        (state.toWord (indexWidth 16 full.length q))) := by
  have hn := RawCandidatePairScan.scan q full containing start hbound hcode left right state hpc ha hl hr
  dsimp only at hn
  have hq : Fits (indexWidth 16 full.length q) q := small_fits _ _ _ (by omega)
  have hconstant (value : Nat) (hv : value ≤ 7) : Fits (indexWidth 16 full.length q) value := small_fits _ _ _ (by omega)
  have hcard (set : Finset (Fin q)) : Fits (indexWidth 16 full.length q) set.card := by
    have h := Finset.card_le_univ set
    simp only [Fintype.card_fin] at h
    exact h.trans_lt hq
  rw [word_run_eq_nat q full containing start hbound hcode left right state hpc ha hl hr hfit hend hwords
    (RawCandidatePairScan.totalSteps full.length left.val right.val q) le_rfl]
  constructor
  · change (BitVec.ofNat _ _).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hconstant 0 (by omega)), hn.1, Nat.mod_eq_of_lt hq]
  · change (BitVec.ofNat _ _).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hconstant 3 (by omega)), hn.2.1, Nat.mod_eq_of_lt hq]
  · change (BitVec.ofNat _ _).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hconstant 4 (by omega)), hn.2.2.1, Nat.mod_eq_of_lt (hcard _)]
  · change (BitVec.ofNat _ _).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hconstant 5 (by omega)), hn.2.2.2.1, Nat.mod_eq_of_lt (hcard _)]
  · change (BitVec.ofNat _ _).toNat = _
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hconstant 6 (by omega)), hn.2.2.2.2.1, Nat.mod_eq_of_lt (hcard _)]
  · intro address h0 h3 h4 h5 h6 h7
    change BitVec.ofNat _ _ = BitVec.ofNat _ _
    exact congrArg (BitVec.ofNat _) (hn.2.2.2.2.2.1 address.toNat h0 h3 h4 h5 h6 h7)
  · change (BitVec.ofNat _ _).toNat = _
    rw [hn.2.2.2.2.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hend]
  · exact hn.2.2.2.2.2.2.2

end Linked

theorem scan_word_append (q : Nat) (full : List (Finset (Fin q))) (front tail : List PackingOp)
    (left right : Fin (full.length + q + 1)) (state : NatState)
    (hpc : state.pc = 5 * front.length) (ha : state.halted = false)
    (hl : state.heap 1 = left.val) (hr : state.heap 2 = right.val)
    (hfit : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (front.length + 125)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode (front ++ programAt front.length ++ tail))) :
    WordScanned full.length q front.length ((RawCandidateOrder.candidateSupports q full).getD left.val ∅)
      ((RawCandidateOrder.candidateSupports q full).getD right.val ∅) (state.toWord (indexWidth 16 full.length q))
      (packingRun (rawIncidenceROM q full) (front ++ programAt front.length ++ tail)
        (RawCandidatePairScan.totalSteps full.length left.val right.val q) (state.toWord (indexWidth 16 full.length q))) :=
  scan_word q full _ front.length (RawCandidatePairScan.append_slice front tail).1
    (RawCandidatePairScan.append_slice front tail).2 left right state hpc ha hl hr hfit hend hwords

end PaperProofs.Structure.LaminarTree.RawCandidatePairScanWord
