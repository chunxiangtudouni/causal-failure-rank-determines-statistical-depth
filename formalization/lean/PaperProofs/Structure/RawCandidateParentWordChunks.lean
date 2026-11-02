module

public import PaperProofs.Structure.RawCandidateParentRAM
public import PaperProofs.Structure.RawCandidateWorkspaceWordMacros
import Mathlib.Tactic.IntervalCases

/-! Exact code slices of the existing parent-search program, and the real
executed prefixes of its small nonrecursive instruction pieces.  The pair query remains the original 125-op dynamic subprogram. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateParentWordChunks

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateParentRAM
open RawIncidenceScanSafety (NatAccessFits)
open RawCandidateOrderingRAM (setWorkspace loadWorkspace storeWorkspace testWorkspace incrementWorkspace testWorkspace_length)

inductive Chunk where
  | initialize | outerTest | initializeChild | innerTest | pairArgs | innerTail | outerTail

def chunkCode (start : Nat) : Chunk → List PackingOp
  | .initialize => setWorkspace 1 0
  | .outerTest => outerTest (start + 361)
  | .initializeChild => initializeChild
  | .innerTest => testWorkspace 2 (start + 346)
  | .pairArgs => pairArguments
  | .innerTail => innerTail start
  | .outerTail => outerTail start

def chunkOffset : Chunk → Nat
  | .initialize => 0 | .outerTest => 6 | .initializeChild => 27 | .innerTest => 64
  | .pairArgs => 77 | .innerTail => 230 | .outerTail => 346

def chunkLength : Chunk → Nat
  | .initialize => 6 | .outerTest => 21 | .initializeChild => 37 | .innerTest => 13
  | .pairArgs => 28 | .innerTail => 116 | .outerTail => 15

def chunkPrefix (start : Nat) : Chunk → List PackingOp
  | .initialize => []
  | .outerTest => setWorkspace 1 0
  | .initializeChild => setWorkspace 1 0 ++ outerTest (start + 361)
  | .innerTest => setWorkspace 1 0 ++ outerTest (start + 361) ++ initializeChild
  | .pairArgs => setWorkspace 1 0 ++ outerTest (start + 361) ++ initializeChild ++ testWorkspace 2 (start + 346)
  | .innerTail => beforePair start ++ RawCandidatePairScan.programAt (start + 105)
  | .outerTail => beforePair start ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start

def chunkSuffix (start : Nat) : Chunk → List PackingOp
  | .initialize => outerTest (start + 361) ++ initializeChild ++ testWorkspace 2 (start + 346) ++ pairArguments ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start
  | .outerTest => initializeChild ++ testWorkspace 2 (start + 346) ++ pairArguments ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start
  | .initializeChild => testWorkspace 2 (start + 346) ++ pairArguments ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start
  | .innerTest => pairArguments ++ RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start
  | .pairArgs => RawCandidatePairScan.programAt (start + 105) ++ innerTail start ++ outerTail start
  | .innerTail => outerTail start
  | .outerTail => []

theorem chunk_code_length (start : Nat) (chunk : Chunk) : (chunkCode start chunk).length = chunkLength chunk := by
  cases chunk <;>
    simp only [chunkCode, chunkLength, setWorkspace_length, outerTest_length, initializeChild_length,
      testWorkspace_length, pairArguments_length, innerTail_length, outerTail_length]

theorem chunk_prefix_length (start : Nat) (chunk : Chunk) :
    (chunkPrefix start chunk).length = chunkOffset chunk := by
  cases chunk <;>
    simp only [chunkPrefix, chunkOffset, List.length_nil, List.length_append,
      setWorkspace_length, outerTest_length, initializeChild_length, testWorkspace_length,
      beforePair_length, RawCandidatePairScan.programAt_length, innerTail_length]

theorem chunk_span (chunk : Chunk) : chunkOffset chunk + chunkLength chunk ≤ 361 := by cases chunk <;> decide

theorem chunk_assembly (start : Nat) (chunk : Chunk) :
    programAt start = chunkPrefix start chunk ++ chunkCode start chunk ++ chunkSuffix start chunk := by
  cases chunk <;>
    simp only [chunkPrefix, chunkCode, chunkSuffix, programAt, beforePair,
      List.nil_append, List.append_nil, List.append_assoc]

theorem chunk_slice (start : Nat) (chunk : Chunk) (position : Nat) (hp : position < chunkLength chunk) :
    (programAt start).getD (chunkOffset chunk + position) paddingOp = (chunkCode start chunk).getD position paddingOp := by
  rw [chunk_assembly start chunk, ← chunk_prefix_length start chunk]
  rw [List.getD_append (chunkPrefix start chunk ++ chunkCode start chunk) (chunkSuffix start chunk) paddingOp _
      (by rw [List.length_append, chunk_code_length]; omega),
    List.getD_append_right (chunkPrefix start chunk) (chunkCode start chunk) paddingOp _ (by omega),
    Nat.add_sub_cancel_left]

def chunkLead (start : Nat) (chunk : Chunk) : List PackingOp :=
  (chunkCode start chunk).take (chunkLength chunk - 1)

def chunkLast (start : Nat) (chunk : Chunk) : PackingOp :=
  (chunkCode start chunk).getD (chunkLength chunk - 1) paddingOp

theorem chunk_lead_length (start : Nat) (chunk : Chunk) : (chunkLead start chunk).length + 1 = chunkLength chunk := by
  rw [chunkLead, List.length_take, chunk_code_length]
  cases chunk <;> decide

theorem chunk_lead_noJump (start : Nat) (chunk : Chunk) : ∀ op ∈ chunkLead start chunk, NoJump op := by
  cases chunk <;>
    simp [chunkLead, chunkCode, chunkLength, setWorkspace, storeWorkspace, testWorkspace,
      loadWorkspace, outerTest, initializeChild, initializeBestCard, initializeParent,
      pairArguments, innerTail, conditionScore, saveBestCard, saveParent, outerTail,
      RawCandidateOrderingRAM.arrayAddress, RawCandidateOrderingRAM.arrayBase,
      RawCandidateOrderingRAM.loadArray, parentAddress, incrementWorkspace,
      loadCell, storeCell, jumpTo, NoJump]

theorem chunk_split (start : Nat) (chunk : Chunk) : chunkCode start chunk =
    chunkLead start chunk ++ [chunkLast start chunk] := by
  have hpos : 0 < chunkLength chunk := by cases chunk <;> decide
  have hlast : chunkLength chunk - 1 < (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [chunkLast, List.getD_eq_getElem _ paddingOp hlast, chunkLead,
    ← List.take_succ_eq_append_getElem hlast]
  have heq : chunkLength chunk - 1 + 1 = (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [heq, List.take_length]

section Linked

variable (rom : PhysicalROM) (containing : List PackingOp) (start : Nat)
  (hbound : start + 361 ≤ containing.length)
  (hcode : ∀ position < 361, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem chunk_run_prefix (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    natRun rom containing count state = runOps rom ((chunkCode start chunk).take count) state := by
  rw [chunk_split start chunk]
  refine RawIncidenceScanSafety.natRun_segment_prefix rom containing (chunkLead start chunk) (chunkLast start chunk)
    (start + chunkOffset chunk)
    (by have hs := chunk_span chunk; have hl := chunk_lead_length start chunk; omega)
    ?_ ?_ (chunk_lead_noJump start chunk) state hpc ha count
    (by have hl := chunk_lead_length start chunk; omega)
  · intro position hp
    have hlen := chunk_lead_length start chunk
    have hpos : position < chunkLength chunk := by omega
    have hh := (hcode (chunkOffset chunk + position) (by have hs := chunk_span chunk; omega)).trans
      (chunk_slice start chunk position hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := chunk_span chunk; omega),
      List.getD_eq_getElem _ _ (by rw [chunk_code_length]; exact hpos)] at hh
    simpa only [Nat.add_assoc, chunkLead, List.getElem_take] using hh
  · have hlen := chunk_lead_length start chunk
    have hpos : (chunkLead start chunk).length < chunkLength chunk := by omega
    have hh := (hcode (chunkOffset chunk + (chunkLead start chunk).length)
      (by have hs := chunk_span chunk; omega)).trans (chunk_slice start chunk _ hpos)
    rw [List.getD_eq_getElem _ _ (by have hs := chunk_span chunk; omega)] at hh
    have heq : (chunkLead start chunk).length = chunkLength chunk - 1 := by omega
    simpa only [Nat.add_assoc, heq, chunkLast] using hh

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateParentWordChunks
