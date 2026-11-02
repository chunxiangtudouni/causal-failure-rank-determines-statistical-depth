module

public import PaperProofs.Structure.RawCandidateOrderingRAM
public import PaperProofs.Structure.RawCandidateWorkspaceWordMacros
public import PaperProofs.Structure.RawCandidateOrderingArrayWord
import Mathlib.Tactic.IntervalCases

/-! Word and physical-access safety for the original fixed count-ranking
program.  Cards and keep flags are the actual preceding phase's tables;
no rank, sorted output, or completed safe run is a caller input. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawCandidateOrderingWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateOrderingRAM
open RawCandidateWorkspaceInit (workspaceBase candidateCount workspaceBase_ge candidateCount_fits)
open RawCandidateWorkspaceBounds (workspaceLimit workspaceLimit_fits workspace_address_fits)
open RawIncidenceScanSafety (NatAccessFits)

inductive Chunk where
  | initialize | outerTest | rowInit | innerTest | compare | innerTail | finishRow | outerTail | finish

def chunkCode (start : Nat) : Chunk → List PackingOp
  | .initialize => initCode
  | .outerTest => testWorkspace 1 (start + 288)
  | .rowInit => rowInit
  | .innerTest => testWorkspace 2 (start + 172)
  | .compare => comparison
  | .innerTail => innerTail start
  | .finishRow => finishRow
  | .outerTail => outerTail start
  | .finish => finishCode

def chunkOffset : Chunk → Nat
  | .initialize => 0 | .outerTest => 9 | .rowInit => 22 | .innerTest => 34
  | .compare => 47 | .innerTail => 157 | .finishRow => 172 | .outerTail => 273 | .finish => 288

def chunkLength : Chunk → Nat
  | .initialize => 9 | .outerTest => 13 | .rowInit => 12 | .innerTest => 13
  | .compare => 110 | .innerTail => 15 | .finishRow => 101 | .outerTail => 15 | .finish => 15

def chunkNumber : Chunk → Nat
  | .initialize => 0 | .outerTest => 1 | .rowInit => 2 | .innerTest => 3
  | .compare => 4 | .innerTail => 5 | .finishRow => 6 | .outerTail => 7 | .finish => 8

def blocks (start : Nat) : List (List PackingOp) :=
  [initCode, testWorkspace 1 (start + 288), rowInit, testWorkspace 2 (start + 172),
    comparison, innerTail start, finishRow, outerTail start, finishCode]

def chunkPrefix (start : Nat) (chunk : Chunk) : List PackingOp :=
  ((blocks start).take (chunkNumber chunk)).flatten

def chunkSuffix (start : Nat) (chunk : Chunk) : List PackingOp :=
  ((blocks start).drop (chunkNumber chunk + 1)).flatten

theorem chunk_code_length (start : Nat) (chunk : Chunk) : (chunkCode start chunk).length = chunkLength chunk := by
  cases chunk <;>
    simp only [chunkCode, chunkLength, initCode_length, testWorkspace_length, rowInit_length,
      comparison_length, innerTail_length, finishRow_length, outerTail_length, finishCode_length]

theorem chunk_prefix_length (start : Nat) (chunk : Chunk) : (chunkPrefix start chunk).length = chunkOffset chunk := by
  cases chunk <;>
    simp only [chunkPrefix, blocks, chunkNumber, chunkOffset, List.take, List.flatten_cons, List.flatten_nil,
      List.append_nil, List.length_append, List.length_nil,
      initCode_length, testWorkspace_length, rowInit_length, comparison_length,
      innerTail_length, finishRow_length, outerTail_length]

theorem chunk_span (chunk : Chunk) : chunkOffset chunk + chunkLength chunk ≤ 303 := by cases chunk <;> decide

theorem chunk_assembly (start : Nat) (chunk : Chunk) :
    programAt start = chunkPrefix start chunk ++ chunkCode start chunk ++ chunkSuffix start chunk := by
  cases chunk <;>
    simp only [programAt, chunkPrefix, chunkSuffix, chunkCode, blocks, chunkNumber,
      List.take, List.drop, List.flatten_cons, List.flatten_nil, List.nil_append, List.append_nil, List.append_assoc]

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
    simp [chunkLead, chunkCode, chunkLength, initCode, rowInit, setWorkspace, storeWorkspace,
      testWorkspace, loadWorkspace, comparison, fetchComparison, compareCards, compareIDs,
      innerTail, outerTail, finishRow, storeOrd, storeInverse, addCount, finishCode,
      incrementWorkspace, arrayBase, arrayAddress, loadArray, storeArray,
      loadCell, storeCell, setCell, jumpTo, NoJump]

theorem chunk_split (start : Nat) (chunk : Chunk) : chunkCode start chunk =
    chunkLead start chunk ++ [chunkLast start chunk] := by
  have hpos : 0 < chunkLength chunk := by cases chunk <;> decide
  have hlast : chunkLength chunk - 1 < (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [chunkLast, List.getD_eq_getElem _ paddingOp hlast, chunkLead,
    ← List.take_succ_eq_append_getElem hlast]
  have heq : chunkLength chunk - 1 + 1 = (chunkCode start chunk).length := by rw [chunk_code_length]; omega
  rw [heq, List.take_length]

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat) (state : NatState) : Prop :=
  RegistersFit (indexWidth 16 full.length q) state ∧
    ∃ offset < 303, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (h : SafePoint q full containing start state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303))) :
    Fits (indexWidth 16 full.length q) state.pc := by
  obtain ⟨offset, hoff, hp, _⟩ := h.2
  rw [hp]
  exact lt_of_le_of_lt (by omega) hend

def MacroSafe (q : Nat) (full : List (Finset (Fin q))) (code : List PackingOp) (state : NatState) : Prop :=
  (∀ count ≤ code.length, RegistersFit (indexWidth 16 full.length q)
    (runOps (rawIncidenceROM q full) (code.take count) state)) ∧
  ∀ count < code.length, NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
    (runOps (rawIncidenceROM q full) (code.take count) state) (code.getD count paddingOp)

theorem MacroSafe.full {q : Nat} {full : List (Finset (Fin q))} {code : List PackingOp} {state : NatState}
    (h : MacroSafe q full code state) :
    RegistersFit (indexWidth 16 full.length q) (runOps (rawIncidenceROM q full) code state) := by
  have hh := h.1 code.length le_rfl
  rwa [List.take_length] at hh

theorem MacroSafe.append {q : Nat} {full : List (Finset (Fin q))} {first second : List PackingOp} {state : NatState}
    (hfirst : MacroSafe q full first state)
    (hsecond : MacroSafe q full second (runOps (rawIncidenceROM q full) first state)) :
    MacroSafe q full (first ++ second) state := by
  constructor
  · intro count hc
    by_cases hsmall : count ≤ first.length
    · rw [List.take_append_of_le_length hsmall]
      exact hfirst.1 count hsmall
    · rw [List.take_append, List.take_of_length_le (by omega), runOps_append]
      apply hsecond.1
      simp only [List.length_append] at hc
      omega
  · intro count hc
    by_cases hsmall : count < first.length
    · rw [List.take_append_of_le_length hsmall.le, List.getD_append _ _ _ _ hsmall]
      exact hfirst.2 count hsmall
    · rw [List.take_append, List.take_of_length_le (by omega), runOps_append,
        List.getD_append_right _ _ _ _ (by omega)]
      apply hsecond.2
      simp only [List.length_append] at hc
      omega

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hf : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hf reg

private theorem scalar_fits (N q value : Nat) (hv : value ≤ 4 * candidateCount N q + 32) :
    Fits (indexWidth 16 N q) value := by
  apply workspace_address_fits
  unfold workspaceLimit
  omega

theorem loadCell_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (cell : Nat)
    (hcell : cell ≤ 8) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hread : Fits (indexWidth 16 full.length q) (state.heap cell)) : MacroSafe q full (loadCell target cell) state := by
  have hfit := scalar_fits full.length q cell (by omega)
  have hlim : cell < workspaceLimit full.length q := by unfold workspaceLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 2 := hc
    interval_cases count
    · exact hf
    · change ∀ reg, Fits _ (Function.update state.register .address cell reg)
      exact fits_update hf .address cell hfit
    · change ∀ reg, Fits _ (Function.update (Function.update state.register .address cell) target (state.heap cell) reg)
      exact fits_update (fits_update hf .address cell hfit) target _ hread
  · intro count hc
    have hc' : count < 2 := hc
    interval_cases count <;>
      simp [loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hlim]

theorem storeCell_safe (q : Nat) (full : List (Finset (Fin q))) (source : Register) (cell : Nat)
    (hcell : cell ≤ 8) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state) :
    MacroSafe q full (storeCell source cell) state := by
  have hfit := scalar_fits full.length q cell (by omega)
  have hlim : cell < workspaceLimit full.length q := by unfold workspaceLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 2 := hc
    interval_cases count
    · exact hf
    · change ∀ reg, Fits _ (Function.update state.register .address cell reg)
      exact fits_update hf .address cell hfit
    · change ∀ reg, Fits _ (Function.update state.register .address cell reg)
      exact fits_update hf .address cell hfit
  · intro count hc
    have hc' : count < 2 := hc
    interval_cases count <;>
      simp [storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits, hlim]

theorem compareCards_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hleft : state.heap 1 ≤ q) (hright : state.heap 2 ≤ q) : MacroSafe q full compareCards state := by
  have hsmall (value : Nat) (hv : value ≤ 2 * q + 8) : Fits (indexWidth 16 full.length q) value :=
    scalar_fits full.length q value (by dsimp [candidateCount]; omega)
  have hlim (cell : Nat) (hc : cell ≤ 8) : cell < workspaceLimit full.length q := by unfold workspaceLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 15 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 15 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by rw [compareCards_length]; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (compareCards[count]'(by rw [compareCards_length]; exact hlt)) _)
      interval_cases count <;>
        simp only [compareCards, loadCell, storeCell, List.getElem_append, List.getElem_cons_zero,
          List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals apply hsmall
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals omega
  · intro count hc
    have hc' : count < 15 := hc
    interval_cases count <;>
      simp [compareCards, loadCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits, hlim]

theorem compareIDs_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hj : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hrank : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (h3 : state.heap 3 ≤ 1) (h4 : state.heap 4 ≤ 1) (h5 : state.heap 5 ≤ 1)
    (hvalue : state.register .value = 1) : MacroSafe q full compareIDs state := by
  have hb := workspaceBase_ge full.length q
  have hlim := workspaceLimit_fits full.length q
  have hoff (offset : Nat) (ho : offset ≤ 3) :
      workspaceBase full.length q + offset < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hcell (cell : Nat) (hc : cell ≤ 8) : cell < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hmin : min 1 (state.heap (workspaceBase full.length q + 1) - state.heap (workspaceBase full.length q + 2)) ≤ 1 := Nat.min_le_left _ _
  have hmul := Nat.mul_le_mul hmin h4
  have hsum : min 1 (state.heap (workspaceBase full.length q + 1) - state.heap (workspaceBase full.length q + 2)) *
      state.heap 4 + state.heap 5 ≤ 2 := by omega
  have hmul2 := Nat.mul_le_mul hsum h3
  rw [Nat.min_comm] at hmul hsum hmul2
  constructor
  · intro count hc
    have hc' : count ≤ 32 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 32 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by rw [compareIDs_length]; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (compareIDs[count]'(by rw [compareIDs_length]; exact hlt)) _)
      interval_cases count <;>
        simp only [compareIDs, loadWorkspace, storeWorkspace, loadCell, List.getElem_append,
          List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute, natArithmetic]
      all_goals apply lt_of_le_of_lt _ hlim
      all_goals unfold workspaceLimit
      all_goals omega
  · intro count hc
    have hc' : count < 32 := hc
    interval_cases count <;>
      simp [compareIDs, loadWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute,
        Instruction.execute, natArithmetic, NatAccessFits, AccessFits, hptr, hoff, hcell]

theorem setWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (offset value : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q) (hv : Fits (indexWidth 16 full.length q) value) :
    MacroSafe q full (setWorkspace offset value) state :=
  ⟨fun count hc => RawCandidateWorkspaceWordMacros.set_prefix_fit q full offset value hoffset state hf hptr hv count hc,
    fun count hc => RawCandidateWorkspaceWordMacros.set_prefix_access q full offset value hoffset state hptr count hc⟩

theorem testWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (counter exit : Nat)
    (hoffset : counter ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hcount : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q)))
    (hcounter : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + counter)))
    (hexit : Fits (indexWidth 16 full.length q) (5 * exit)) : MacroSafe q full (testWorkspace counter exit) state :=
  ⟨fun count hc => RawCandidateWorkspaceWordMacros.test_prefix_fit q full counter exit hoffset state hf hptr hcount hcounter hexit count hc,
    fun count hc => RawCandidateWorkspaceWordMacros.test_prefix_access q full counter exit hoffset state hptr count hc⟩

theorem incrementWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hinc : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + offset) + 1)) :
    MacroSafe q full (incrementWorkspace offset) state :=
  ⟨fun count hc => RawCandidateWorkspaceWordMacros.increment_prefix_fit q full offset hoffset state hf hptr hinc count hc,
    fun count hc => RawCandidateWorkspaceWordMacros.increment_prefix_access q full offset hoffset state hptr count hc⟩

theorem single_safe (q : Nat) (full : List (Finset (Fin q))) (op : PackingOp) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hnext : RegistersFit (indexWidth 16 full.length q) (natExecuteOp (rawIncidenceROM q full) op state))
    (hx : NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) state op) :
    MacroSafe q full [op] state := by
  constructor
  · intro count hc
    have hc' : count ≤ 1 := hc
    interval_cases count
    · exact hf
    · exact hnext
  · intro count hc
    have hc' : count < 1 := hc
    interval_cases count
    exact hx

theorem constant_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (value : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) (hv : Fits (indexWidth 16 full.length q) value) :
    MacroSafe q full [.base (.base (.constant target value))] state := by
  apply single_safe q full _ state hf
  · exact fits_update hf target value hv
  · trivial

theorem setCell_safe (q : Nat) (full : List (Finset (Fin q))) (cell value : Nat)
    (hcell : cell ≤ 8) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hv : Fits (indexWidth 16 full.length q) value) : MacroSafe q full (setCell cell value) state := by
  have first := constant_safe q full .total value state hf hv
  exact first.append (storeCell_safe q full .total cell hcell _ first.full)

theorem initialize_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q) : MacroSafe q full initCode state := by
  have first := setCell_safe q full 0 0 (by omega) state hf (scalar_fits _ _ _ (by omega))
  have hp : (runOps (rawIncidenceROM q full) (setCell 0 0) state).heap 8 = workspaceBase full.length q := by
    simpa [setCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute] using hptr
  exact first.append (setWorkspace_safe q full 1 0 (by omega) _ first.full hp (scalar_fits _ _ _ (by omega)))

theorem rowInit_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q) : MacroSafe q full rowInit state := by
  have first := setWorkspace_safe q full 2 0 (by omega) state hf hptr (scalar_fits _ _ _ (by omega))
  have hb := workspaceBase_ge full.length q
  have hp : (runOps (rawIncidenceROM q full) (setWorkspace 2 0) state).heap 8 = workspaceBase full.length q := by
    simp [setWorkspace, storeWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hptr,
      show 8 ≠ workspaceBase full.length q + 2 by omega]
  exact first.append (setWorkspace_safe q full 3 0 (by omega) _ first.full hp (scalar_fits _ _ _ (by omega)))

theorem jump_safe (q : Nat) (full : List (Finset (Fin q))) (target : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (ht : Fits (indexWidth 16 full.length q) (5 * target)) : MacroSafe q full (jumpTo target) state := by
  have zero := scalar_fits full.length q 0 (by omega)
  constructor
  · intro count hc
    have hc' : count ≤ 3 := hc
    interval_cases count
    · exact hf
    · exact fits_update hf .flag 0 zero
    · exact fits_update (fits_update hf .flag 0 zero) .index (5 * target) ht
    · exact fits_update (fits_update hf .flag 0 zero) .index (5 * target) ht
  · intro count hc
    have hc' : count < 3 := hc
    interval_cases count <;> trivial

theorem tail_safe (q : Nat) (full : List (Finset (Fin q))) (counter target : Nat)
    (hoffset : counter ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hinc : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + counter) + 1))
    (ht : Fits (indexWidth 16 full.length q) (5 * target)) :
    MacroSafe q full (incrementWorkspace counter ++ jumpTo target) state := by
  have first := incrementWorkspace_safe q full counter hoffset state hf hptr hinc
  exact first.append (jump_safe q full target _ first.full ht)

def OrdFits (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  ∀ position < candidateCount full.length q,
    Fits (indexWidth 16 full.length q)
      (state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 2 position))

theorem OrdFits.of_heap_eq {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (h : OrdFits q full before) (hh : after.heap = before.heap) : OrdFits q full after := by
  intro position hp
  rw [hh]
  exact h position hp

theorem OrdFits.of_innerFrame {q : Nat} {full : List (Finset (Fin q))} {before after : NatState}
    (h : OrdFits q full before) (frame : InnerFrame (workspaceBase full.length q) before after) : OrdFits q full after := by
  intro position hp
  have hb := workspaceBase_ge full.length q
  rw [frame _ (by unfold arraySlot; omega) (by unfold arraySlot; omega)
    (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
    (by unfold arraySlot; omega) (by unfold arraySlot; omega)]
  exact h position hp

theorem rankCount_le (card : Nat → Nat) (keep : Nat → Bool) (candidate upto : Nat) :
    rankCount card keep candidate upto ≤ upto := by
  simpa only [rankCount, List.length_range] using List.length_filter_le
    (fun other => keep other && decide (Precedes card other candidate)) (List.range upto)

theorem comparison_middle_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hj : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hrank : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (hleft : state.heap 1 ≤ q) (hright : state.heap 2 ≤ q) (hkeep : state.heap 3 ≤ 1) :
    MacroSafe q full (compareCards ++ compareIDs) state := by
  have first := compareCards_safe q full state hf hleft hright
  let compared := runOps (rawIncidenceROM q full) compareCards state
  have effects := compareCards_effect (rawIncidenceROM q full) state
  have hh : compared.heap = Function.update
      (Function.update state.heap 4 (1 - min 1 ((state.heap 1 - state.heap 2) + (state.heap 2 - state.heap 1))))
      5 (min 1 (state.heap 1 - state.heap 2)) := effects.1
  have hb := workspaceBase_ge full.length q
  have frame (address : Nat) (h4 : address ≠ 4) (h5 : address ≠ 5) : compared.heap address = state.heap address := by
    rw [hh, Function.update_of_ne h5, Function.update_of_ne h4]
  apply first.append
  apply compareIDs_safe q full compared first.full
  · exact (frame 8 (by omega) (by omega)).trans hptr
  · rw [frame _ (by omega) (by omega)]
    exact hi
  · rw [frame _ (by omega) (by omega)]
    exact hj
  · rw [frame _ (by omega) (by omega)]
    exact hrank
  · rw [frame 3 (by omega) (by omega)]
    exact hkeep
  · rw [hh]
    simp only [Function.update_of_ne (by omega : 4 ≠ 5), Function.update_self]
    omega
  · rw [hh, Function.update_self]
    exact Nat.min_le_left _ _
  · exact effects.2

theorem candidateCard_le (q : Nat) (full : List (Finset (Fin q))) (index : Nat) :
    RawCandidateStableOrder.candidateCard q full index ≤ q := by
  have hh := Finset.card_le_univ ((RawCandidateOrder.candidateSupports q full).getD index ∅)
  simpa only [RawCandidateStableOrder.candidateCard, Fintype.card_fin] using hh

theorem bit_le_one (value : Bool) : bit value ≤ 1 := by cases value <;> decide

theorem loadWorkspace_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (offset : Nat)
    (hoffset : offset ≤ 3) (state : NatState) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hread : Fits (indexWidth 16 full.length q) (state.heap (workspaceBase full.length q + offset))) :
    MacroSafe q full (loadWorkspace target offset) state :=
  ⟨fun count hc => RawCandidateWorkspaceWordMacros.load_prefix_fit q full target offset hoffset state hf hptr hread count hc,
    fun count hc => RawCandidateWorkspaceWordMacros.load_prefix_access q full target offset hoffset state hptr count hc⟩

def inverseValueCode : List PackingOp :=
  loadWorkspace .total 3 ++ [.base (.base (.constant .old 1)), .base (.base (.add .total .total .old))] ++
    loadCell .old 3 ++ [.arithmetic .multiply .total .total .old]

theorem inverseValueCode_length : inverseValueCode.length = 10 := rfl

theorem inverseValueCode_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hrank : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (hkeep : state.heap 3 ≤ 1) : MacroSafe q full inverseValueCode state := by
  have hb := workspaceBase_ge full.length q
  have hlim := workspaceLimit_fits full.length q
  have hmul := Nat.mul_le_mul (Nat.succ_le_succ hrank) hkeep
  have hoff : workspaceBase full.length q + 3 < workspaceLimit full.length q := by unfold workspaceLimit; omega
  have hcell (cell : Nat) (hc : cell ≤ 8) : cell < workspaceLimit full.length q := by unfold workspaceLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 10 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 10 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by rw [inverseValueCode_length]; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (inverseValueCode[count]'(by rw [inverseValueCode_length]; exact hlt)) _)
      interval_cases count <;>
        simp only [inverseValueCode, loadWorkspace, loadCell, List.getElem_append,
          List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute, natArithmetic]
      all_goals apply lt_of_le_of_lt _ hlim
      all_goals unfold workspaceLimit
      all_goals omega
  · intro count hc
    have hc' : count < 10 := hc
    interval_cases count <;>
      simp [inverseValueCode, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, hptr, hoff, hcell]

theorem addCount_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hcount : state.heap 0 ≤ candidateCount full.length q) (hkeep : state.heap 3 ≤ 1) : MacroSafe q full addCount state := by
  have hlim := workspaceLimit_fits full.length q
  have hcell (cell : Nat) (hc : cell ≤ 8) : cell < workspaceLimit full.length q := by unfold workspaceLimit; omega
  constructor
  · intro count hc
    have hc' : count ≤ 7 := hc
    induction count with
    | zero => exact hf
    | succ count ih =>
      have hlt : count < 7 := by omega
      have hp := ih hlt.le hlt.le
      rw [List.take_succ_eq_append_getElem (by change count < 7; exact hlt), runOps_append]
      change RegistersFit _ (natExecuteOp _ (addCount[count]'(by change count < 7; exact hlt)) _)
      interval_cases count <;>
        simp only [addCount, loadCell, storeCell, List.getElem_append,
          List.getElem_cons_zero, List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, Op.execute, Instruction.execute]
      all_goals first | exact hp | apply fits_update hp
      all_goals simp_all [runOps, natExecuteOp, Op.execute, Instruction.execute]
      all_goals apply lt_of_le_of_lt _ hlim
      all_goals unfold workspaceLimit
      all_goals omega
  · intro count hc
    have hc' : count < 7 := hc
    interval_cases count <;>
      simp [addCount, loadCell, storeCell, runOps, natExecuteOp, Op.execute,
        Instruction.execute, NatAccessFits, AccessFits, hcell]

theorem storeCell_heap (rom : PhysicalROM) (source : Register) (cell : Nat) (state : NatState)
    (hsource : source ≠ .address) :
    (runOps rom (storeCell source cell) state).heap = Function.update state.heap cell (state.register source) := by
  simp [storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, hsource]

def fetchOne (factor counter cell : Nat) : List PackingOp := loadArray .total factor counter ++ storeCell .total cell

theorem fetchOne_heap (rom : PhysicalROM) (factor counter cell : Nat) (state : NatState) :
    (runOps rom (fetchOne factor counter cell) state).heap = Function.update state.heap cell
      (state.heap (arraySlot (state.heap 8) (state.heap (state.heap 8)) factor (state.heap (state.heap 8 + counter)))) := by
  rw [fetchOne, runOps_append, storeCell_heap rom .total cell _ (by decide),
    loadArray_heap, loadArray_value]

theorem fetched_heap_preserved (rom : PhysicalROM) (factor counter cell address : Nat) (state : NatState)
    (hne : address ≠ cell) :
    (runOps rom (fetchOne factor counter cell) state).heap address = state.heap address := by
  rw [fetchOne_heap, Function.update_of_ne hne]

theorem loadArray_safe (q : Nat) (full : List (Finset (Fin q))) (target : Register) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (hsource : Fits (indexWidth 16 full.length q) (state.heap (arraySlot (workspaceBase full.length q)
      (candidateCount full.length q) factor (state.heap (workspaceBase full.length q + counter))))) :
    MacroSafe q full (loadArray target factor counter) state :=
  ⟨fun count hc => RawCandidateOrderingArrayWord.loadArray_prefix_fit q full target factor counter hfactor hcounter state
      hf hptr hheader hindex hsource count (by rwa [loadArray_length] at hc),
    fun count hc => RawCandidateOrderingArrayWord.loadArray_prefix_access q full target factor counter hfactor hcounter state
      hptr hheader hindex count (by rwa [loadArray_length] at hc)⟩

theorem storeArray_safe (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q) :
    MacroSafe q full (storeArray factor counter) state :=
  ⟨fun count hc => RawCandidateOrderingArrayWord.storeArray_prefix_fit q full factor counter hfactor hcounter state
      hf hptr hheader hindex count (by rwa [storeArray_length] at hc),
    fun count hc => RawCandidateOrderingArrayWord.storeArray_prefix_access q full factor counter hfactor hcounter state
      hptr hheader hindex count (by rwa [storeArray_length] at hc)⟩

theorem fetchOne_safe (q : Nat) (full : List (Finset (Fin q))) (factor counter cell : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (hcell : cell ≤ 8) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hindex : state.heap (workspaceBase full.length q + counter) ≤ candidateCount full.length q)
    (hsource : Fits (indexWidth 16 full.length q) (state.heap (arraySlot (workspaceBase full.length q)
      (candidateCount full.length q) factor (state.heap (workspaceBase full.length q + counter))))) :
    MacroSafe q full (fetchOne factor counter cell) state := by
  have first := loadArray_safe q full .total factor counter hfactor hcounter state hf hptr hheader hindex hsource
  exact first.append (storeCell_safe q full .total cell hcell _ first.full)

theorem fetchComparison_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hj : state.heap (workspaceBase full.length q + 2) ≤ candidateCount full.length q)
    (hleft : Fits (indexWidth 16 full.length q) (state.heap (arraySlot (workspaceBase full.length q)
      (candidateCount full.length q) 0 (state.heap (workspaceBase full.length q + 1)))))
    (hright : Fits (indexWidth 16 full.length q) (state.heap (arraySlot (workspaceBase full.length q)
      (candidateCount full.length q) 0 (state.heap (workspaceBase full.length q + 2)))))
    (hkeep : Fits (indexWidth 16 full.length q) (state.heap (arraySlot (workspaceBase full.length q)
      (candidateCount full.length q) 1 (state.heap (workspaceBase full.length q + 2))))) :
    MacroSafe q full fetchComparison state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  let one := runOps rom (fetchOne 0 1 1) state
  have f1 (address : Nat) (ha : 8 ≤ address) : one.heap address = state.heap address :=
    fetched_heap_preserved rom 0 1 1 address state (by omega)
  have s1 := fetchOne_safe q full 0 1 1 (by omega) (by omega) (by omega) state hf hptr hheader hi hleft
  have s2 := fetchOne_safe q full 0 2 2 (by omega) (by omega) (by omega) one s1.full
    ((f1 8 le_rfl).trans hptr) ((f1 B (by omega)).trans hheader) (by rw [f1 _ (by omega)]; exact hj)
    (by rw [f1 (B + 2) (by omega), f1 _ (by unfold arraySlot; omega)]; exact hright)
  let two := runOps rom (fetchOne 0 2 2) one
  have f2 (address : Nat) (ha : 8 ≤ address) : two.heap address = state.heap address :=
    (fetched_heap_preserved rom 0 2 2 address one (by omega)).trans (f1 address ha)
  have s3 := fetchOne_safe q full 1 2 3 (by omega) (by omega) (by omega) two s2.full
    ((f2 8 le_rfl).trans hptr) ((f2 B (by omega)).trans hheader) (by rw [f2 _ (by omega)]; exact hj)
    (by rw [f2 (B + 2) (by omega), f2 _ (by unfold arraySlot; omega)]; exact hkeep)
  have allSafe := (s1.append s2).append (by simpa only [runOps_append] using s3)
  simpa only [fetchComparison, fetchOne, List.append_assoc] using allSafe

theorem comparison_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) < candidateCount full.length q)
    (hj : state.heap (workspaceBase full.length q + 2) < candidateCount full.length q)
    (hrank : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state) :
    MacroSafe q full comparison state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  have lc := htables.1 _ hi
  have rc := htables.1 _ hj
  have kc := htables.2 _ hj
  have lv : state.heap (arraySlot B M 0 (state.heap (B + 1))) ≤ q := by rw [lc]; exact candidateCard_le _ _ _
  have rv : state.heap (arraySlot B M 0 (state.heap (B + 2))) ≤ q := by rw [rc]; exact candidateCard_le _ _ _
  have kv : state.heap (arraySlot B M 1 (state.heap (B + 2))) ≤ 1 := by rw [kc]; exact bit_le_one _
  have qfit : Fits (indexWidth 16 full.length q) q := scalar_fits _ _ _ (by dsimp [candidateCount]; omega)
  have first := fetchComparison_safe q full state hf hptr hheader hi.le hj.le
    (lv.trans_lt qfit) (rv.trans_lt qfit) (kv.trans_lt (scalar_fits _ _ 1 (by omega)))
  let fetched := runOps rom fetchComparison state
  have hh := fetchComparison_heap rom state (by rw [hptr]; exact hb)
  change fetched.heap = Function.update (Function.update (Function.update state.heap 1 _) 2 _) 3 _ at hh
  rw [hptr, hheader] at hh
  have frame (address : Nat) (ha : 8 ≤ address) : fetched.heap address = state.heap address := by
    rw [hh]
    simp only [Function.update_of_ne (by omega : address ≠ 3),
      Function.update_of_ne (by omega : address ≠ 2), Function.update_of_ne (by omega : address ≠ 1)]
  rw [comparison, List.append_assoc]
  apply first.append
  apply comparison_middle_safe q full fetched first.full
  · exact (frame 8 le_rfl).trans hptr
  · rw [frame _ (by omega)]; exact hi.le
  · rw [frame _ (by omega)]; exact hj.le
  · rw [frame _ (by omega)]; exact hrank
  · rw [hh]; simpa using lv
  · rw [hh]; simpa using rv
  · rw [hh]; simpa using kv

theorem select_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state) :
    MacroSafe q full [.base (.base (.select .total .flag .total .old))] state := by
  apply single_safe q full _ state hf
  · apply fits_update hf
    change Fits _ (if state.register .flag = 0 then state.register .old else state.register .total)
    split <;> exact hf _
  · trivial

theorem storeOrd_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) < candidateCount full.length q)
    (hrank : state.heap (workspaceBase full.length q + 3) < candidateCount full.length q)
    (hkeep : state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 1
      (state.heap (workspaceBase full.length q + 1))) ≤ 1)
    (horder : Fits (indexWidth 16 full.length q) (state.heap (arraySlot (workspaceBase full.length q)
      (candidateCount full.length q) 2 (state.heap (workspaceBase full.length q + 3))))) :
    MacroSafe q full storeOrd state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  let loadedKeep := runOps rom (loadArray .flag 1 1) state
  have s1 := loadArray_safe q full .flag 1 1 (by omega) (by omega) state hf hptr hheader hi.le
    (scalar_fits _ _ _ (by omega))
  have h1 : loadedKeep.heap = state.heap := loadArray_heap rom .flag 1 1 state
  let saved := runOps rom (storeCell .flag 3) loadedKeep
  have s2 := storeCell_safe q full .flag 3 (by omega) loadedKeep s1.full
  have h2 : saved.heap = Function.update state.heap 3
      (state.heap (arraySlot B M 1 (state.heap (B + 1)))) := by
    rw [show saved = runOps rom (storeCell .flag 3) loadedKeep from rfl,
      storeCell_heap rom .flag 3 _ (by decide), h1, loadArray_value, hptr, hheader]
  have frame (address : Nat) (ha : 8 ≤ address) : saved.heap address = state.heap address := by
    rw [h2, Function.update_of_ne (by omega : address ≠ 3)]
  let loadedID := runOps rom (loadWorkspace .total 1) saved
  have s3 := loadWorkspace_safe q full .total 1 (by omega) saved s2.full ((frame 8 le_rfl).trans hptr)
    (by rw [frame _ (by omega)]; exact scalar_fits _ _ _ (by omega))
  have h3 : loadedID.heap = saved.heap := by
    change (runOps rom (loadWorkspace .total 1) saved).heap = saved.heap
    rw [loadWorkspace_runOps]
    rfl
  have idframe (address : Nat) (ha : 8 ≤ address) : loadedID.heap address = state.heap address :=
    (congrFun h3 address).trans (frame address ha)
  let oldOrd := runOps rom (loadArray .old 2 3) loadedID
  have s4 := loadArray_safe q full .old 2 3 (by omega) (by omega) loadedID s3.full
    ((idframe 8 le_rfl).trans hptr) ((idframe B (by omega)).trans hheader)
    (by rw [idframe _ (by omega)]; exact hrank.le)
    (by rw [idframe (B + 3) (by omega), idframe _ (by unfold arraySlot; omega)]; exact horder)
  have h4 : oldOrd.heap = loadedID.heap := loadArray_heap rom .old 2 3 loadedID
  have oldframe (address : Nat) (ha : 8 ≤ address) : oldOrd.heap address = state.heap address :=
    (congrFun h4 address).trans (idframe address ha)
  let selected := natExecuteOp rom (.base (.base (.select .total .flag .total .old))) oldOrd
  have s5 := select_safe q full oldOrd s4.full
  have sh : selected.heap = oldOrd.heap := rfl
  have s6 := storeArray_safe q full 2 3 (by omega) (by omega) selected s5.full
    ((congrFun sh 8).trans ((oldframe 8 le_rfl).trans hptr))
    ((congrFun sh B).trans ((oldframe B (by omega)).trans hheader))
    (by rw [sh, oldframe _ (by omega)]; exact hrank.le)
  have allSafe := s1.append (s2.append (s3.append (s4.append (s5.append s6))))
  simpa only [storeOrd, List.append_assoc] using allSafe

theorem storeInverse_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) ≤ candidateCount full.length q)
    (hrank : state.heap (workspaceBase full.length q + 3) ≤ candidateCount full.length q)
    (hkeep : state.heap 3 ≤ 1) : MacroSafe q full storeInverse state := by
  let rom := rawIncidenceROM q full
  let computed := runOps rom inverseValueCode state
  have first := inverseValueCode_safe q full state hf hptr hrank hkeep
  have hh : computed.heap = state.heap := by
    simp [computed, inverseValueCode, loadWorkspace, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  have second := storeArray_safe q full 3 1 (by omega) (by omega) computed first.full
    ((congrFun hh 8).trans hptr) ((congrFun hh _).trans hheader) (by rw [hh]; exact hi)
  simpa only [storeInverse, inverseValueCode, List.append_assoc] using first.append second

theorem finishRow_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hi : state.heap (workspaceBase full.length q + 1) < candidateCount full.length q)
    (hrank : state.heap (workspaceBase full.length q + 3) < candidateCount full.length q)
    (hkeep : state.heap (arraySlot (workspaceBase full.length q) (candidateCount full.length q) 1
      (state.heap (workspaceBase full.length q + 1))) ≤ 1)
    (horder : Fits (indexWidth 16 full.length q) (state.heap (arraySlot (workspaceBase full.length q)
      (candidateCount full.length q) 2 (state.heap (workspaceBase full.length q + 3)))))
    (hcount : state.heap 0 ≤ candidateCount full.length q) : MacroSafe q full finishRow state := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  let ordered := runOps rom storeOrd state
  have first := storeOrd_safe q full state hf hptr hheader hi hrank hkeep horder
  have ho := storeOrd_heap rom state (by rw [hptr]; exact hb)
  dsimp only at ho
  rw [hptr, hheader] at ho
  change ordered.heap = _ at ho
  have frame (address : Nat) (ha : address < B) (h3 : address ≠ 3) : ordered.heap address = state.heap address := by
    rw [ho, Function.update_of_ne (by unfold arraySlot; omega), Function.update_of_ne h3]
  have controls (offset : Nat) (hoff : offset ≤ 3) : ordered.heap (B + offset) = state.heap (B + offset) := by
    rw [ho, Function.update_of_ne (by unfold arraySlot; omega), Function.update_of_ne (by omega : B + offset ≠ 3)]
  have ok : ordered.heap 3 ≤ 1 := by
    rw [ho, Function.update_of_ne (by unfold arraySlot; omega), Function.update_self]
    exact hkeep
  have second := storeInverse_safe q full ordered first.full ((frame 8 (by omega) (by omega)).trans hptr)
    (by simpa only [Nat.add_zero] using (controls 0 (by omega)).trans hheader)
    (by rw [controls 1 (by omega)]; exact hi.le) (by rw [controls 3 (by omega)]; exact hrank.le) ok
  let inversed := runOps rom storeInverse ordered
  have ih := storeInverse_heap rom ordered
  change inversed.heap = _ at ih
  have ib : ordered.heap 8 = B := (frame 8 (by omega) (by omega)).trans hptr
  have im : ordered.heap B = M := by simpa only [Nat.add_zero] using (controls 0 (by omega)).trans hheader
  rw [ib, im] at ih
  have ic : inversed.heap 0 ≤ M := by
    rw [ih, Function.update_of_ne (by unfold arraySlot; omega), frame 0 (by omega) (by omega)]
    exact hcount
  have ik : inversed.heap 3 ≤ 1 := by
    rw [ih, Function.update_of_ne (by unfold arraySlot; omega)]
    exact ok
  have third := addCount_safe q full inversed second.full ic ik
  have allSafe := first.append (second.append third)
  simpa only [finishRow, List.append_assoc] using allSafe

theorem finishCode_safe (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (hcount : state.heap 0 ≤ candidateCount full.length q) : MacroSafe q full finishCode state := by
  let rom := rawIncidenceROM q full
  have first := loadCell_safe q full .total 0 (by omega) state hf (scalar_fits _ _ _ (by omega))
  let loaded := runOps rom (loadCell .total 0) state
  have lh : loaded.heap = state.heap := rfl
  have bp : loaded.heap 8 = workspaceBase full.length q := (congrFun lh 8).trans hptr
  have bm : loaded.heap (workspaceBase full.length q) = candidateCount full.length q := (congrFun lh _).trans hheader
  have base : MacroSafe q full (arrayBase 4) loaded :=
    ⟨fun count hc => RawCandidateOrderingArrayWord.arrayBase_prefix_fit q full 4 (by omega) loaded first.full bp bm count
        (by rwa [arrayBase_length] at hc),
      fun count hc => RawCandidateOrderingArrayWord.arrayBase_prefix_access q full 4 loaded bp count
        (by rwa [arrayBase_length] at hc)⟩
  let addressed := runOps rom (arrayBase 4) loaded
  have ba := RawCandidateOrderingArrayWord.arrayBase_effect q full 4 loaded bp bm
  have last : MacroSafe q full [.base (.base (.storeHeap .address .total))] addressed := by
    apply single_safe q full (.base (.base (.storeHeap .address .total))) addressed base.full
    · exact base.full
    · change addressed.register .address < workspaceLimit full.length q
      rw [ba.1]
      unfold workspaceLimit
      omega
  have allSafe := first.append (base.append last)
  simpa only [finishCode, List.append_assoc] using allSafe

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 303 ≤ containing.length)
  (hcode : ∀ position < 303, containing.getD (start + position) paddingOp = (programAt start).getD position paddingOp)

include hbound hcode

theorem outer_iteration_ordFits (index : Nat) (state : NatState)
    (ready : OuterReady (workspaceBase full.length q) (candidateCount full.length q) index (5 * (start + 9)) state)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hi : index < candidateCount full.length q) (hord : OrdFits q full state) :
    OrdFits q full (natRun (rawIncidenceROM q full) containing
      (138 * candidateCount full.length q + 154) state) := by
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  let rank := rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) index M
  have hb : 16 ≤ B := workspaceBase_ge full.length q
  have hrank : rank < M := rankCount_lt _ _ _ _ hi
  have hn := RawCandidateOrderingRAM.outer_iteration (rawIncidenceROM q full) containing start hbound hcode B M index
    (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state hb ready htables hi
  dsimp only at hn
  obtain ⟨_rn, _tables, _count, _inverse, order, frame⟩ := hn
  intro position hp
  by_cases heq : position = rank
  · subst position
    rw [order]
    split
    · exact scalar_fits _ _ _ (by omega)
    · exact hord rank hrank
  · rw [frame (arraySlot B M 2 position)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by unfold arraySlot; omega) (by unfold arraySlot; omega)
      (by unfold arraySlot; omega) (by intro _; unfold arraySlot; omega)]
    exact hord position hp

theorem outer_scan_partial_ordFits (state : NatState)
    (ready : OuterReady (workspaceBase full.length q) (candidateCount full.length q) 0 (5 * (start + 9)) state)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hzero : state.heap 0 = 0) (hord : OrdFits q full state)
    (upto : Nat) (hupto : upto ≤ candidateCount full.length q) :
    OrdFits q full (natRun (rawIncidenceROM q full) containing
      ((138 * candidateCount full.length q + 154) * upto) state) := by
  revert hupto
  induction upto with
  | zero => intro _; exact hord
  | succ upto ih =>
    intro hupto
    have prior := ih (by omega)
    have pn := RawCandidateOrderingRAM.outer_scan_partial (rawIncidenceROM q full) containing start hbound hcode q full
      (workspaceBase full.length q) state (workspaceBase_ge _ _) ready htables hzero upto ((Nat.le_succ upto).trans hupto)
    dsimp only at pn
    rw [Nat.mul_succ, natRun_add]
    exact outer_iteration_ordFits q full containing start hbound hcode upto _ pn.1 pn.2.1 (by omega) prior

theorem chunk_run_prefix (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    natRun (rawIncidenceROM q full) containing count state =
      runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state := by
  rw [chunk_split start chunk]
  refine RawIncidenceScanSafety.natRun_segment_prefix (rawIncidenceROM q full) containing
    (chunkLead start chunk) (chunkLast start chunk) (start + chunkOffset chunk)
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

theorem chunk_run (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false) :
    natRun (rawIncidenceROM q full) containing (chunkLength chunk) state =
      runOps (rawIncidenceROM q full) (chunkCode start chunk) state := by
  rw [chunk_run_prefix q full containing start hbound hcode chunk state hpc ha (chunkLength chunk) le_rfl,
    List.take_of_length_le (by rw [chunk_code_length])]

theorem chunk_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hf : ∀ count ≤ chunkLength chunk, RegistersFit (indexWidth 16 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state))
    (hx : ∀ count < chunkLength chunk, NatAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)
      ((chunkCode start chunk).getD count paddingOp)) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  constructor
  · intro count hc
    have hr := chunk_run_prefix q full containing start hbound hcode chunk state hpc ha count hc.le
    have hsmall : count ≤ chunkLength chunk - 1 := by omega
    have heq : (chunkCode start chunk).take count = (chunkLead start chunk).take count := by
      rw [chunkLead, List.take_take, min_eq_left hsmall]
    have hno : ∀ op ∈ (chunkCode start chunk).take count, NoJump op := by
      rw [heq]
      exact fun op hop => chunk_lead_noJump start chunk op (List.mem_of_mem_take hop)
    have hp : (natRun (rawIncidenceROM q full) containing count state).pc =
        5 * (start + chunkOffset chunk + count) := by
      rw [hr, runOps_pc _ _ _ hno,
        List.length_take_of_le (by rw [chunk_code_length]; omega), hpc]
      omega
    have hs := chunk_span chunk
    refine ⟨?_, chunkOffset chunk + count, by omega, ?_, ?_,
      (chunkCode start chunk).getD count paddingOp, ?_, ?_⟩
    · rw [hr]
      exact hf count hc.le
    · rw [hp]
      omega
    · rw [hr, runOps_halted, ha]
    · rw [hp, natFetch_body containing (start + chunkOffset chunk + count) (by omega), decode_encode]
      have hh := (hcode (chunkOffset chunk + count) (by omega)).trans (chunk_slice start chunk count hc)
      rw [List.getD_eq_getElem _ paddingOp (by omega)] at hh
      simpa only [Nat.add_assoc] using congrArg some hh
    · rw [hr]
      exact hx count hc
  · rw [chunk_run q full containing start hbound hcode chunk state hpc ha]
    have hh := hf _ le_rfl
    rwa [List.take_of_length_le (by rw [chunk_code_length])] at hh

theorem chunk_of_macro (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hm : MacroSafe q full (chunkCode start chunk) state) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  apply chunk_safe q full containing start hbound hcode chunk state hpc ha
  · intro count hc
    exact hm.1 count (by rw [chunk_code_length]; exact hc)
  · intro count hc
    exact hm.2 count (by rw [chunk_code_length]; exact hc)

theorem inner_iteration_safe (left right rank : Nat) (state : NatState)
    (ready : RankReady (workspaceBase full.length q) (candidateCount full.length q) left right rank
      (5 * (start + 34)) state)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < candidateCount full.length q) (hr : right < candidateCount full.length q)
    (hrank : rank ≤ candidateCount full.length q)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state 138 ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing 138 state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  let tested := runOps rom (testWorkspace 2 (start + 172)) state
  have ht := testWorkspace_effect rom 2 (start + 172) state
  have th : tested.heap = state.heap := ht.1
  have rt : RankReady B M left right rank (5 * (start + 47)) tested := by
    refine ⟨(congrFun th _).trans ready.base_cell, (congrFun th _).trans ready.count_cell,
      (congrFun th _).trans ready.left_cell, (congrFun th _).trans ready.right_cell,
      (congrFun th _).trans ready.rank_cell, ?_, ht.2.2.trans ready.active⟩
    have hp := ht.2.1
    rw [ready.base_cell, ready.count_cell, ready.right_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hr), ready.pc] at hp
    change tested.pc = _ at hp
    omega
  have tt : InputTables B M (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) tested := by
    rw [InputTables, th]
    exact htables
  have ss := chunk_of_macro q full containing start hbound hcode .innerTest state ready.pc ready.active
    (testWorkspace_safe q full 2 (start + 172) (by omega) state hf ready.base_cell
      (by rw [ready.count_cell]; exact candidateCount_fits _ _)
      (by rw [ready.right_cell]; exact scalar_fits _ _ _ (by omega))
      (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .innerTest state ready.pc ready.active] at ss
  have cm := comparison_safe q full tested ss.2 rt.base_cell rt.count_cell
    (by rw [rt.left_cell]; exact hl) (by rw [rt.right_cell]; exact hr)
    (by rw [rt.rank_cell]; exact hrank) tt
  have cs := chunk_of_macro q full containing start hbound hcode .compare tested rt.pc rt.active cm
  rw [chunk_run q full containing start hbound hcode .compare tested rt.pc rt.active] at cs
  let compared := runOps rom comparison tested
  have cn := comparison_ready rom start B M left right rank (RawCandidateStableOrder.candidateCard q full)
    (RawCandidateOrder.keepCandidate q full) tested hb rt tt hl hr
  have rc := cn.1
  have tm := tail_safe q full 2 (start + 34) (by omega) compared cs.2 rc.base_cell
    (by rw [rc.right_cell]; exact scalar_fits _ _ _ (by omega)) (lt_of_le_of_lt (by omega) hend)
  have ts := chunk_of_macro q full containing start hbound hcode .innerTail compared rc.pc rc.active tm
  dsimp only [chunkLength] at ss cs ts
  have runTest : natRun rom containing 13 state = tested :=
    run_innerTest rom containing start hbound hcode state ready.pc ready.active
  have runCompare : natRun rom containing 110 tested = compared :=
    run_comparison rom containing start hbound hcode tested rt.pc rt.active
  have remainder : PrefixSafe (SafePoint q full containing start) rom containing tested (110 + 15) := by
    apply PrefixSafe.add _ _ _ _ _ _ cs.1
    rw [runCompare]
    exact ts.1
  constructor
  · change PrefixSafe _ _ _ _ (13 + (110 + 15))
    apply PrefixSafe.add _ _ _ _ _ _ ss.1
    rw [runTest]
    exact remainder
  · rw [show 138 = 13 + (110 + 15) by decide, natRun_add, runTest, natRun_add, runCompare]
    exact ts.2

theorem rank_scan_partial_safe (left : Nat) (state : NatState)
    (ready : RankReady (workspaceBase full.length q) (candidateCount full.length q) left 0 0 (5 * (start + 34)) state)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < candidateCount full.length q)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303)))
    (upto : Nat) (hupto : upto ≤ candidateCount full.length q) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (138 * upto) ∧
      RegistersFit (indexWidth 16 full.length q) (natRun (rawIncidenceROM q full) containing (138 * upto) state) := by
  revert hupto
  induction upto with
  | zero => intro _; exact ⟨by intro clock hc; omega, hf⟩
  | succ upto ih =>
    intro hupto
    obtain ⟨safe, fits⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing (138 * upto) state
    have pn := RawCandidateOrderingRAM.rank_scan_partial (rawIncidenceROM q full) containing start hbound hcode
      (workspaceBase full.length q) (candidateCount full.length q) left (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state (workspaceBase_ge _ _) ready htables hl upto (by omega)
    have step := inner_iteration_safe q full containing start hbound hcode left upto _ previous pn.1 pn.2.1 hl
      (by omega) ((rankCount_le _ _ _ _).trans (by omega)) fits hend
    constructor
    · rw [Nat.mul_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [Nat.mul_succ, natRun_add]
      exact step.2

theorem rank_scan_safe (left : Nat) (state : NatState)
    (ready : RankReady (workspaceBase full.length q) (candidateCount full.length q) left 0 0 (5 * (start + 34)) state)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < candidateCount full.length q)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (138 * candidateCount full.length q + 13) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (138 * candidateCount full.length q + 13) state) := by
  let M := candidateCount full.length q
  have ss := rank_scan_partial_safe q full containing start hbound hcode left state ready htables hl hf hend M le_rfl
  have sn := RawCandidateOrderingRAM.rank_scan_partial (rawIncidenceROM q full) containing start hbound hcode
    (workspaceBase full.length q) M left (RawCandidateStableOrder.candidateCard q full)
    (RawCandidateOrder.keepCandidate q full) state (workspaceBase_ge _ _) ready htables hl M le_rfl
  let previous := natRun (rawIncidenceROM q full) containing (138 * M) state
  have rp := sn.1
  have ts := chunk_of_macro q full containing start hbound hcode .innerTest previous rp.pc rp.active
    (testWorkspace_safe q full 2 (start + 172) (by omega) previous ss.2 rp.base_cell
      (by rw [rp.count_cell]; exact candidateCount_fits _ _)
      (by rw [rp.right_cell]; exact candidateCount_fits _ _) (lt_of_le_of_lt (by omega) hend))
  constructor
  · exact PrefixSafe.add _ _ _ _ _ _ ss.1 ts.1
  · rw [natRun_add]
    exact ts.2

theorem outer_iteration_safe (left : Nat) (state : NatState)
    (ready : OuterReady (workspaceBase full.length q) (candidateCount full.length q) left (5 * (start + 9)) state)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hl : left < candidateCount full.length q) (hcount : state.heap 0 ≤ candidateCount full.length q)
    (hord : OrdFits q full state) (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (138 * candidateCount full.length q + 154) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (138 * candidateCount full.length q + 154) state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  let tested := runOps rom (testWorkspace 1 (start + 288)) state
  have ht := testWorkspace_effect rom 1 (start + 288) state
  have th : tested.heap = state.heap := ht.1
  have tp : tested.pc = 5 * (start + 22) := by
    have hp := ht.2.1
    rw [ready.base_cell, ready.count_cell, ready.left_cell,
      ite_eq_right (Nat.sub_ne_zero_of_lt hl), ready.pc] at hp
    change tested.pc = _ at hp
    omega
  have ta : tested.halted = false := ht.2.2.trans ready.active
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest state ready.pc ready.active
    (testWorkspace_safe q full 1 (start + 288) (by omega) state hf ready.base_cell
      (by rw [ready.count_cell]; exact candidateCount_fits _ _)
      (by rw [ready.left_cell]; exact scalar_fits _ _ _ (by omega)) (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .outerTest state ready.pc ready.active] at ts
  let initialized := runOps rom rowInit tested
  have init := chunk_of_macro q full containing start hbound hcode .rowInit tested tp ta
    (rowInit_safe q full tested ts.2 ((congrFun th 8).trans ready.base_cell))
  rw [chunk_run q full containing start hbound hcode .rowInit tested tp ta] at init
  have ih : initialized.heap = Function.update (Function.update state.heap (B + 2) 0) (B + 3) 0 := by
    have hh := rowInit_heap rom tested (by rw [th, ready.base_cell]; exact hb)
    simpa only [th, ready.base_cell] using hh
  have ri : RankReady B M left 0 0 (5 * (start + 34)) initialized := by
    constructor
    · rw [ih]; simpa (disch := omega) using ready.base_cell
    · rw [ih]; simpa using ready.count_cell
    · rw [ih]; simpa using ready.left_cell
    · rw [ih]; simp
    · rw [ih]; simp
    · rw [show initialized = runOps rom rowInit tested from rfl,
        runOps_pc rom rowInit tested (by simp [rowInit, setWorkspace, storeWorkspace, loadCell, NoJump]), rowInit_length, tp]
      omega
    · exact (runOps_halted _ _ _).trans ta
  have fi : InnerFrame B state initialized := by
    intro address hj hr _h1 _h2 _h3 _h4 _h5
    rw [ih]
    simp [hj, hr]
  have ti := InputTables.of_innerFrame B M _ _ hb htables fi
  have rs := rank_scan_safe q full containing start hbound hcode left initialized ri ti hl init.2 hend
  have rn := RawCandidateOrderingRAM.rank_scan rom containing start hbound hcode B M left
    (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) initialized hb ri ti hl
  let ranked := natRun rom containing (138 * M + 13) initialized
  have rr := rn.1
  have tr := rn.2.1
  have fr : InnerFrame B state ranked := InnerFrame.trans B fi rn.2.2
  have ordf : OrdFits q full ranked := hord.of_innerFrame fr
  let rank := rankCount (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) left M
  have hrank : rank < M := rankCount_lt _ _ _ _ hl
  have rankedKeep : ranked.heap (arraySlot B M 1 (ranked.heap (B + 1))) ≤ 1 := by
    rw [rr.left_cell, tr.2 left hl]
    exact bit_le_one _
  have rankedOrd : Fits (indexWidth 16 full.length q)
      (ranked.heap (arraySlot B M 2 (ranked.heap (B + 3)))) := by
    rw [rr.rank_cell]
    exact ordf rank hrank
  have rankedCount : ranked.heap 0 ≤ M := by
    rw [fr 0 (by omega) (by omega) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hcount
  have fm := finishRow_safe q full ranked rs.2 rr.base_cell rr.count_cell
    (by rw [rr.left_cell]; exact hl) (by rw [rr.rank_cell]; exact hrank) rankedKeep rankedOrd rankedCount
  have fs := chunk_of_macro q full containing start hbound hcode .finishRow ranked rr.pc rr.active fm
  rw [chunk_run q full containing start hbound hcode .finishRow ranked rr.pc rr.active] at fs
  let written := runOps rom finishRow ranked
  have wn := finishRow_ready rom start B M left M rank (RawCandidateStableOrder.candidateCard q full)
    (RawCandidateOrder.keepCandidate q full) ranked hb rr tr hl hrank
  have rw' := wn.1
  have tm := tail_safe q full 1 (start + 9) (by omega) written fs.2 rw'.base_cell
    (by rw [rw'.left_cell]; exact scalar_fits _ _ _ (by omega)) (lt_of_le_of_lt (by omega) hend)
  have tail := chunk_of_macro q full containing start hbound hcode .outerTail written rw'.pc rw'.active tm
  dsimp only [chunkLength] at ts init fs tail
  have runTest : natRun rom containing 13 state = tested := run_outerTest rom containing start hbound hcode state ready.pc ready.active
  have runInit : natRun rom containing 12 tested = initialized := run_rowInit rom containing start hbound hcode tested tp ta
  have runFinish : natRun rom containing 101 ranked = written := run_finishRow rom containing start hbound hcode ranked rr.pc rr.active
  have finishSafe : PrefixSafe (SafePoint q full containing start) rom containing ranked (101 + 15) := by
    apply PrefixSafe.add _ _ _ _ _ _ fs.1
    rw [runFinish]
    exact tail.1
  have rankSafe : PrefixSafe (SafePoint q full containing start) rom containing initialized ((138 * M + 13) + (101 + 15)) :=
    PrefixSafe.add _ _ _ _ _ _ rs.1 finishSafe
  have initSafe : PrefixSafe (SafePoint q full containing start) rom containing tested (12 + ((138 * M + 13) + (101 + 15))) := by
    apply PrefixSafe.add _ _ _ _ _ _ init.1
    rw [runInit]
    exact rankSafe
  have hclock : 138 * M + 154 = 13 + (12 + ((138 * M + 13) + (101 + 15))) := by omega
  constructor
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact initSafe
  · rw [hclock, natRun_add, runTest, natRun_add, runInit, natRun_add]
    change RegistersFit _ (natRun rom containing (101 + 15) ranked)
    rw [natRun_add, runFinish]
    exact tail.2

omit hbound hcode in
theorem processedCount_le (keep : Nat → Bool) (upto : Nat) : processedCount keep upto ≤ upto := by
  simpa only [processedCount, List.length_range] using List.length_filter_le keep (List.range upto)

theorem outer_scan_partial_safe (state : NatState)
    (ready : OuterReady (workspaceBase full.length q) (candidateCount full.length q) 0 (5 * (start + 9)) state)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hzero : state.heap 0 = 0) (hord : OrdFits q full state)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303)))
    (upto : Nat) (hupto : upto ≤ candidateCount full.length q) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        ((138 * candidateCount full.length q + 154) * upto) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing ((138 * candidateCount full.length q + 154) * upto) state) := by
  revert hupto
  induction upto with
  | zero => intro _; exact ⟨by intro clock hc; omega, hf⟩
  | succ upto ih =>
    intro hupto
    obtain ⟨safe, fits⟩ := ih (by omega)
    let previous := natRun (rawIncidenceROM q full) containing ((138 * candidateCount full.length q + 154) * upto) state
    have pn := RawCandidateOrderingRAM.outer_scan_partial (rawIncidenceROM q full) containing start hbound hcode q full
      (workspaceBase full.length q) state (workspaceBase_ge _ _) ready htables hzero upto ((Nat.le_succ upto).trans hupto)
    have po := outer_scan_partial_ordFits q full containing start hbound hcode state ready htables hzero hord upto (by omega)
    have pcEq : previous.heap 0 = processedCount (RawCandidateOrder.keepCandidate q full) upto := pn.2.2.1.counter
    have pc : previous.heap 0 ≤ candidateCount full.length q := by
      rw [pcEq]
      exact (processedCount_le _ _).trans (by omega)
    have step := outer_iteration_safe q full containing start hbound hcode upto previous pn.1 pn.2.1 (by omega) pc po fits hend
    constructor
    · rw [Nat.mul_succ]
      exact PrefixSafe.add _ _ _ _ _ _ safe step.1
    · rw [Nat.mul_succ, natRun_add]
      exact step.2

/-- The complete dynamic count-ranking program is prefix-safe from the
actual retention tables and ordinary initial ord-word bounds. -/
theorem sort_nat_safe (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state
        (totalSteps (candidateCount full.length q)) ∧
      RegistersFit (indexWidth 16 full.length q)
        (natRun (rawIncidenceROM q full) containing (totalSteps (candidateCount full.length q)) state) := by
  let rom := rawIncidenceROM q full
  let B := workspaceBase full.length q
  let M := candidateCount full.length q
  have hb : 16 ≤ B := workspaceBase_ge _ _
  let initialized := runOps rom initCode state
  have init := chunk_of_macro q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha (initialize_safe q full state hf hptr)
  rw [chunk_run q full containing start hbound hcode .initialize state
    (by simpa only [chunkOffset, Nat.add_zero] using hpc) ha] at init
  have ih : initialized.heap = Function.update (Function.update state.heap 0 0) (B + 1) 0 := by
    simpa only [hptr] using initCode_heap rom state
  have ri : OuterReady B M 0 (5 * (start + 9)) initialized := by
    constructor
    · rw [ih]; simpa (disch := omega) using hptr
    · rw [ih]; simpa (disch := omega) using hheader
    · rw [ih]; simp
    · rw [show initialized = runOps rom initCode state from rfl,
        runOps_pc rom initCode state (by simp [initCode, setCell, storeCell, setWorkspace, storeWorkspace, loadCell, NoJump]),
        initCode_length, hpc]
      omega
    · exact (runOps_halted _ _ _).trans ha
  have ti : InputTables B M (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) initialized := by
    constructor
    · intro index hi
      rw [ih]
      simpa (disch := omega) [arraySlot] using htables.1 index hi
    · intro index hi
      rw [ih]
      simpa (disch := omega) [arraySlot] using htables.2 index hi
  have oi : OrdFits q full initialized := by
    intro position hp
    rw [ih]
    simpa (disch := omega) [arraySlot] using hord position hp
  have iz : initialized.heap 0 = 0 := by rw [ih]; simp (disch := omega)
  have scan := outer_scan_partial_safe q full containing start hbound hcode initialized ri ti iz oi init.2 hend M le_rfl
  have sn := RawCandidateOrderingRAM.outer_scan_partial rom containing start hbound hcode q full B initialized hb ri ti iz M le_rfl
  let scanned := natRun rom containing ((138 * M + 154) * M) initialized
  have rs : OuterReady B M M (5 * (start + 9)) scanned := sn.1
  have ts := chunk_of_macro q full containing start hbound hcode .outerTest scanned rs.pc rs.active
    (testWorkspace_safe q full 1 (start + 288) (by omega) scanned scan.2 rs.base_cell
      (by rw [rs.count_cell]; exact candidateCount_fits _ _)
      (by rw [rs.left_cell]; exact candidateCount_fits _ _) (lt_of_le_of_lt (by omega) hend))
  rw [chunk_run q full containing start hbound hcode .outerTest scanned rs.pc rs.active] at ts
  let tested := runOps rom (testWorkspace 1 (start + 288)) scanned
  have ht := testWorkspace_effect rom 1 (start + 288) scanned
  have th : tested.heap = scanned.heap := ht.1
  have tp : tested.pc = 5 * (start + 288) := by
    simpa only [rs.base_cell, rs.count_cell, rs.left_cell, Nat.sub_self, ite_true] using ht.2.1
  have ta : tested.halted = false := ht.2.2.trans rs.active
  have countEq : scanned.heap 0 = processedCount (RawCandidateOrder.keepCandidate q full) M := sn.2.2.1.counter
  have tc : tested.heap 0 ≤ M := by
    rw [th, countEq]
    exact processedCount_le _ _
  have fm := finishCode_safe q full tested ts.2 ((congrFun th 8).trans rs.base_cell)
    ((congrFun th B).trans rs.count_cell) tc
  have fs := chunk_of_macro q full containing start hbound hcode .finish tested tp ta fm
  dsimp only [chunkLength] at init ts fs
  have runInit : natRun rom containing 9 state = initialized := run_initCode rom containing start hbound hcode state hpc ha
  have runTest : natRun rom containing 13 scanned = tested := run_outerTest rom containing start hbound hcode scanned rs.pc rs.active
  have rest : PrefixSafe (SafePoint q full containing start) rom containing scanned (13 + 15) := by
    apply PrefixSafe.add _ _ _ _ _ _ ts.1
    rw [runTest]
    exact fs.1
  have afterInit : PrefixSafe (SafePoint q full containing start) rom containing initialized
      (((138 * M + 154) * M) + (13 + 15)) := PrefixSafe.add _ _ _ _ _ _ scan.1 rest
  have hclock : totalSteps M = 9 + (((138 * M + 154) * M) + (13 + 15)) := by
    rw [totalSteps, Nat.mul_comm M (138 * M + 154)]
    omega
  constructor
  · rw [hclock]
    apply PrefixSafe.add _ _ _ _ _ _ init.1
    rw [runInit]
    exact afterInit
  · rw [hclock, natRun_add, runInit, natRun_add]
    change RegistersFit _ (natRun rom containing (13 + 15) scanned)
    rw [natRun_add, runTest]
    exact fs.2

theorem natRun_prefix_safe (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303)))
    (count : Nat) (hc : count ≤ totalSteps (candidateCount full.length q)) :
    let result := natRun (rawIncidenceROM q full) containing count state
    RegistersFit (indexWidth 16 full.length q) result ∧ Fits (indexWidth 16 full.length q) result.pc ∧ result.halted = false := by
  have hs := sort_nat_safe q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend
  by_cases heq : count = totalSteps (candidateCount full.length q)
  · subst count
    have hn : Sorted q full (workspaceBase full.length q) start state
        (natRun (rawIncidenceROM q full) containing (totalSteps (candidateCount full.length q)) state) :=
      RawCandidateOrderingRAM.sort (rawIncidenceROM q full) containing start hbound hcode q full
        (workspaceBase full.length q) state (workspaceBase_ge _ _) hptr hheader htables hpc ha
    exact ⟨hs.2, by rw [hn.returned.pc]; exact hend, hn.returned.active⟩
  · have hp := hs.1 count (by omega)
    obtain ⟨offset, hoff, pc, active, _⟩ := hp.2
    exact ⟨hp.1, by rw [pc]; exact lt_of_le_of_lt (by omega) hend, active⟩

theorem word_run_eq_nat (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ totalSteps (candidateCount full.length q)) :
    packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q)) =
      (natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q) := by
  apply natRun_toWord _ _ _ count hwords
  intro k hk
  have hs := natRun_prefix_safe q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend k (by omega)
  exact ⟨hs.1, hs.2.1⟩

theorem word_prefix_safe (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing))
    (count : Nat) (hc : count < totalSteps (candidateCount full.length q)) :
    let after := packingRun (rawIncidenceROM q full) containing count (state.toWord (indexWidth 16 full.length q))
    after.halted = false ∧ after.pc.toNat + 4 < (packingCode containing).length ∧
      ∃ offset < 303, after.pc.toNat = 5 * (start + offset) ∧
        ∃ op, PackingOp.decode (fetch containing after) = some op ∧
          packingAccessFits (rawIncidenceROM q full) (workspaceLimit full.length q) after op := by
  have hp := (sort_nat_safe q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend).1 count hc
  have pcFit := hp.pcFits hend
  obtain ⟨offset, hoff, pointer, active, op, decoded, access⟩ := hp.2
  dsimp only
  rw [word_run_eq_nat q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend hwords count hc.le]
  have hpcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord (indexWidth 16 full.length q)).pc.toNat =
      5 * (start + offset) := by
    change (BitVec.ofNat _ _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pointer]
  refine ⟨active, ?_, offset, hoff, hpcWord, op, ?_, ?_⟩
  · rw [hpcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch _ (packingCode containing)
      (BitVec.ofNat _ (natRun (rawIncidenceROM q full) containing count state).pc).toNat) = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, physicalFetch_eq _ _ _ hwords]
    exact decoded
  · exact physical_access_of_nat _ (workspaceLimit full.length q) _ _ hp.1 access

theorem sort_word (state : NatState)
    (hf : RegistersFit (indexWidth 16 full.length q) state)
    (hptr : state.heap 8 = workspaceBase full.length q)
    (hheader : state.heap (workspaceBase full.length q) = candidateCount full.length q)
    (htables : InputTables (workspaceBase full.length q) (candidateCount full.length q)
      (RawCandidateStableOrder.candidateCard q full) (RawCandidateOrder.keepCandidate q full) state)
    (hord : OrdFits q full state) (hpc : state.pc = 5 * start) (ha : state.halted = false)
    (hend : Fits (indexWidth 16 full.length q) (5 * (start + 303)))
    (hwords : WordsFit (indexWidth 16 full.length q) (packingCode containing)) :
    let result := natRun (rawIncidenceROM q full) containing (totalSteps (candidateCount full.length q)) state
    packingRun (rawIncidenceROM q full) containing (totalSteps (candidateCount full.length q))
        (state.toWord (indexWidth 16 full.length q)) = result.toWord (indexWidth 16 full.length q) ∧
      Sorted q full (workspaceBase full.length q) start state result :=
  ⟨word_run_eq_nat q full containing start hbound hcode state hf hptr hheader htables hord hpc ha hend hwords _ le_rfl,
    RawCandidateOrderingRAM.sort (rawIncidenceROM q full) containing start hbound hcode q full
      (workspaceBase full.length q) state (workspaceBase_ge _ _) hptr hheader htables hpc ha⟩

end Linked

end PaperProofs.Structure.LaminarTree.RawCandidateOrderingWord
