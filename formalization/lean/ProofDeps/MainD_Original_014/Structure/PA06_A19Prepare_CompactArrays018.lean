module

public import Structure.PA06_A19Prepare_CompactMacros014
public import Structure.PA06_A19Prepare_CompactCandidates007
public import PaperProofs.Structure.RawCandidateOrderingArrayWord
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Actual compact B16 array-macro prefixes. The original fixed ISA bodies
are retained; every real load/store address is bounded by the LINEAR008
allocation. Caller registers use their complete width32, including values
which do not fit width16. No whole-loop Word refinement is claimed here.
The eight original array helper boundaries are proved from actual count,
counter and loaded-word facts. The logical index may equal M at a loop end;
the physical allocation bound still holds for such prefixes. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactArrays018

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateOrderingRAM
open RawIncidenceScanSafety (NatAccessFits)

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

theorem linearLimit_fits (N q : Nat) : Fits (indexWidth 32 N q) (linearLimit N q) :=
  PA06A19PrepareCompactWord008.fits_width32_of_width16 N q _
    (PA06A19PrepareCompactWord008.linearLimit_fits N q)

private theorem fits_update {bits : Nat} {registers : Register → Nat}
    (hr : ∀ reg, Fits bits (registers reg)) (target : Register) (value : Nat) (hv : Fits bits value) :
    ∀ reg, Fits bits (Function.update registers target value reg) := by
  intro reg
  by_cases heq : reg = target
  · simpa only [heq, Function.update_self] using hv
  · simpa only [Function.update_of_ne heq] using hr reg

theorem arrayBase_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (factor : Nat) (hfactor : factor ≤ 4)
    (state : NatState) (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (count : Nat) (hc : count ≤ 12) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((arrayBase factor).take count) state) := by
  have hlimit := linearLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (full.length + q + 1) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 12 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 12; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((arrayBase factor)[count]'(by change count < 12; exact hlt)) _)
    interval_cases count <;>
      simp only [arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)

theorem arrayBase_prefix_access (q : Nat) (full : List (Finset (Fin q))) (factor : Nat)
    (state : NatState) (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 12) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((arrayBase factor).take count) state)
      ((arrayBase factor).getD count paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hB : 16 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  interval_cases count <;>
    simp [arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, h8, hB]

theorem arrayAddress_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1))
    (count : Nat) (hc : count ≤ 18) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((arrayAddress factor counter).take count) state) := by
  have hlimit := linearLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (full.length + q + 1) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 18 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 18; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((arrayAddress factor counter)[count]'(by change count < 18; exact hlt)) _)
    interval_cases count <;>
      simp only [arrayAddress, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)

theorem arrayAddress_prefix_access (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hcounter : counter ≤ 3) (state : NatState) (hptr : state.heap 8 = 16)
    (count : Nat) (hc : count < 18) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((arrayAddress factor counter).take count) state)
      ((arrayAddress factor counter).getD count paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hB : 16 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr : 16 + counter < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  interval_cases count <;>
    simp [arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, h8, hB, haddr]

theorem loadArray_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1))
    (hsource : Fits (indexWidth 32 full.length q)
      (state.heap (arraySlot 16 (full.length + q + 1) factor
        (state.heap (16 + counter)))))
    (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target factor counter).take count) state) := by
  have hlimit := linearLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (full.length + q + 1) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 19 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 19; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((loadArray target factor counter)[count]'(by change count < 19; exact hlt)) _)
    interval_cases count <;>
      simp only [loadArray, arrayAddress, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute, arraySlot])
    all_goals apply lt_of_le_of_lt _ hlimit
    all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
    all_goals nlinarith

theorem storeArray_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1))
    (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((storeArray factor counter).take count) state) := by
  have hlimit := linearLimit_fits full.length q
  have hmul := Nat.mul_le_mul_left (full.length + q + 1) hfactor
  induction count with
  | zero => exact hr
  | succ count ih =>
    have hlt : count < 19 := by omega
    have hp := ih hlt.le
    rw [List.take_succ_eq_append_getElem (by change count < 19; exact hlt), runOps_append]
    change RegistersFit _ (natExecuteOp _ ((storeArray factor counter)[count]'(by change count < 19; exact hlt)) _)
    interval_cases count <;>
      simp only [storeArray, arrayAddress, arrayBase, loadWorkspace, loadCell, List.getElem_append, List.getElem_cons_zero,
        List.getElem_cons_succ, List.length_append, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, RegistersFit, natExecuteOp, natArithmetic, Op.execute, Instruction.execute]
    all_goals first | exact hp | apply fits_update hp
    all_goals first
      | (apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)
      | (simp_all [runOps, natExecuteOp, natArithmetic, Op.execute, Instruction.execute];
          apply lt_of_le_of_lt _ hlimit; unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; nlinarith)

theorem loadArray_prefix_access (q : Nat) (full : List (Finset (Fin q))) (target : Register) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1))
    (count : Nat) (hc : count < 19) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target factor counter).take count) state)
      ((loadArray target factor counter).getD count paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hB : 16 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr : 16 + counter < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hm := Nat.mul_le_mul_left (full.length + q + 1) hfactor
  interval_cases count <;>
    simp [loadArray, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hheader, h8, hB, haddr]
  all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
  all_goals nlinarith

theorem storeArray_prefix_access (q : Nat) (full : List (Finset (Fin q))) (factor counter : Nat)
    (hfactor : factor ≤ 4) (hcounter : counter ≤ 3) (state : NatState)
    (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = (full.length + q + 1))
    (hindex : state.heap (16 + counter) ≤ (full.length + q + 1))
    (count : Nat) (hc : count < 19) :
    NatAccessFits (rawIncidenceROM q full) (linearLimit full.length q)
      (runOps (rawIncidenceROM q full) ((storeArray factor counter).take count) state)
      ((storeArray factor counter).getD count paddingOp) := by
  have h8 : 8 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hB : 16 < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have haddr : 16 + counter < linearLimit full.length q := by unfold linearLimit PA06A19PrepareCompactWord008.linearLimit; omega
  have hm := Nat.mul_le_mul_left (full.length + q + 1) hfactor
  interval_cases count <;>
    simp [storeArray, arrayAddress, arrayBase, loadWorkspace, loadCell, runOps, natExecuteOp, natArithmetic,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, hptr, hheader, h8, hB, haddr]
  all_goals unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
  all_goals nlinarith


/-- Numeric source bounds do not impose a width16 restriction on any
incoming caller register. -/
theorem value_le_count_fits (N q value : Nat) (hv : value ≤ N + q + 1) :
    Fits (indexWidth 32 N q) value := by
  apply lt_trans ?_ (linearLimit_fits N q)
  unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
  omega

/-- The scalar loader is the exact same five instructions in014. Its
source qualification follows from the actual counter value. -/
theorem counter_load_prefix_fit (q : Nat) (full : List (Finset (Fin q)))
    (target : Register) (counter : Nat) (hoffset : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (hptr : state.heap 8 = 16)
    (hcounter : state.heap (16 + counter) ≤ full.length + q + 1)
    (count : Nat) (hc : count ≤ 5) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((loadWorkspace target counter).take count) state) :=
  PA06A19PrepareCompactMacros014.load_prefix_fit q full target counter hoffset state hr hptr
    (value_le_count_fits _ _ _ hcounter) count hc

theorem counter_set_prefix_fit (q : Nat) (full : List (Finset (Fin q)))
    (counter value : Nat) (hoffset : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (hptr : state.heap 8 = 16)
    (hvalue : value ≤ full.length + q + 1) (count : Nat) (hc : count ≤ 6) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((setWorkspace counter value).take count) state) :=
  PA06A19PrepareCompactMacros014.set_prefix_fit q full counter value hoffset state hr hptr
    (value_le_count_fits _ _ _ hvalue) count hc

theorem counter_increment_prefix_fit (q : Nat) (full : List (Finset (Fin q)))
    (counter : Nat) (hoffset : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (hptr : state.heap 8 = 16)
    (hcounter : state.heap (16 + counter) < full.length + q + 1)
    (count : Nat) (hc : count ≤ 12) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((incrementWorkspace counter).take count) state) :=
  PA06A19PrepareCompactMacros014.increment_prefix_fit q full counter hoffset state hr hptr
    (value_le_count_fits _ _ _ (by omega)) count hc

theorem counter_test_prefix_fit (q : Nat) (full : List (Finset (Fin q)))
    (counter exit : Nat) (hoffset : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state) (hptr : state.heap 8 = 16)
    (hheader : state.heap 16 = full.length + q + 1)
    (hcounter : state.heap (16 + counter) ≤ full.length + q + 1)
    (hexit : Fits (indexWidth 32 full.length q) (5 * exit)) (count : Nat) (hc : count ≤ 13) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((testWorkspace counter exit).take count) state) :=
  PA06A19PrepareCompactMacros014.test_prefix_fit q full counter exit hoffset state hr hptr
    (value_le_count_fits _ _ _ (by rw [hheader]))
    (value_le_count_fits _ _ _ hcounter) hexit count hc

theorem card_word_fits {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (tables : InputTables 16 (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (index : Nat) (hi : index < full.length + q + 1) :
    Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16 (full.length + q + 1) 0 index)) := by
  rw [tables.1 index hi]
  have hcard : RawCandidateStableOrder.candidateCard q full index ≤ q := by
    simpa only [RawCandidateStableOrder.candidateCard, Fintype.card_fin] using
      Finset.card_le_univ ((RawCandidateOrder.candidateSupports q full).getD index ∅)
  exact value_le_count_fits _ _ _ (by omega)

theorem keep_word_fits {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (tables : InputTables 16 (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (index : Nat) (hi : index < full.length + q + 1) :
    Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16 (full.length + q + 1) 1 index)) := by
  rw [tables.2 index hi]
  have hbit : bit (RawCandidateOrder.keepCandidate q full index) ≤ 1 := by
    cases RawCandidateOrder.keepCandidate q full index <;> decide
  exact value_le_count_fits _ _ _ (by omega)

theorem order_word_fits {q : Nat} {full : List (Finset (Fin q))} {nodes : Nat}
    {order inverse : Nat → Nat} {state : NatState}
    (tables : RawCandidateParentRAM.InputTables q full 16 nodes order inverse state)
    (node : Nat) (hn : node < nodes) :
    Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16 (full.length + q + 1) 2 node)) := by
  rw [tables.ordered node hn]
  exact value_le_count_fits _ _ _ (tables.order_valid node hn).le

/-- A source-data bound on actual cached inverse words. This is proved
from Sorted.output.inverse and preserved by the original parent kernel. -/
def InverseValuesBound (q : Nat) (full : List (Finset (Fin q))) (state : NatState) : Prop :=
  ∀ index < full.length + q + 1,
    state.heap (arraySlot 16 (full.length + q + 1) 3 index) ≤ full.length + q + 1

theorem inverseValuesBound_of_sorted {q : Nat} {full : List (Finset (Fin q))}
    {sortStart : Nat} {before state : NatState}
    (sorted : Sorted q full 16 sortStart before state) : InverseValuesBound q full state := by
  intro index hi
  rw [sorted.output.inverse index hi]
  split
  · exact Nat.succ_le_of_lt (RawCandidateRankScan.lessCount_lt_candidateCount q full index hi)
  · omega

theorem inverse_word_fits {q : Nat} {full : List (Finset (Fin q))} {state : NatState}
    (actual : InverseValuesBound q full state) (index : Nat) (hi : index < full.length + q + 1) :
    Fits (indexWidth 32 full.length q) (state.heap (arraySlot 16 (full.length + q + 1) 3 index)) :=
  value_le_count_fits _ _ _ (actual index hi)

/-- No supplied source word Fits is needed for a card cache load. -/
theorem card_load_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register)
    (counter : Nat) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (tables : InputTables 16 (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hindex : state.heap (16 + counter) < full.length + q + 1)
    (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target 0 counter).take count) state) :=
  loadArray_prefix_fit q full target 0 counter (by decide) hcounter state hr hptr hheader hindex.le
    (card_word_fits tables _ hindex) count hc

theorem keep_load_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register)
    (counter : Nat) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (tables : InputTables 16 (full.length + q + 1) (RawCandidateStableOrder.candidateCard q full)
      (RawCandidateOrder.keepCandidate q full) state)
    (hindex : state.heap (16 + counter) < full.length + q + 1)
    (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target 1 counter).take count) state) :=
  loadArray_prefix_fit q full target 1 counter (by decide) hcounter state hr hptr hheader hindex.le
    (keep_word_fits tables _ hindex) count hc

theorem order_load_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register)
    (counter : Nat) (hcounter : counter ≤ 3) (nodes : Nat) (order inverse : Nat → Nat) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (tables : RawCandidateParentRAM.InputTables q full 16 nodes order inverse state)
    (hindex : state.heap (16 + counter) < nodes) (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target 2 counter).take count) state) :=
  loadArray_prefix_fit q full target 2 counter (by decide) hcounter state hr tables.base_cell tables.count_cell
    (hindex.le.trans tables.nodes_le) (order_word_fits tables _ hindex) count hc

theorem inverse_load_prefix_fit (q : Nat) (full : List (Finset (Fin q))) (target : Register)
    (counter : Nat) (hcounter : counter ≤ 3) (state : NatState)
    (hr : RegistersFit (indexWidth 32 full.length q) state)
    (hptr : state.heap 8 = 16) (hheader : state.heap 16 = full.length + q + 1)
    (actual : InverseValuesBound q full state)
    (hindex : state.heap (16 + counter) < full.length + q + 1) (count : Nat) (hc : count ≤ 19) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((loadArray target 3 counter).take count) state) :=
  loadArray_prefix_fit q full target 3 counter (by decide) hcounter state hr hptr hheader hindex.le
    (inverse_word_fits actual _ hindex) count hc

open PA06A19PrepareCompactCandidates007

/-- Same actual parent endpoint as007, with the inverse-value bound retained
from the real sorter output. The caller supplies only original positive-q
and laminar input qualifications, not a source-value or safety premise. -/
theorem parent_entry_with_inverse (tail : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ clock ≤ parentClockBound q full,
      let actual := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      ParentEntry q full actual ∧ InverseValuesBound q full actual := by
  let count := full.length + q + 1
  let nodes := (RawCandidateOrder.retainedCandidateIndices q full).length
  obtain ⟨first, hfirst, sorted, hzero⟩ := Metadata.sorted_entry
    (RawCandidateParentRAM.programAt parentStart ++ tail) q full hl
  let before := natRun (rawIncidenceROM q full) (program tail) first natInitial
  let sortedClock := first + RawCandidateOrderingRAM.totalSteps count
  let sortedState := natRun (rawIncidenceROM q full) (program tail) sortedClock natInitial
  have hs : Sorted q full 16 Metadata.orderingStart before sortedState := sorted
  let order := RawCandidateParentRAM.observedOrder q full 16 sortedState
  let inverse := RawCandidateParentRAM.observedInverse q full 16 sortedState
  let parentSteps := RawCandidateParentRAM.totalSteps full.length q nodes order
  have ht := RawCandidateParentRAM.InputTables.of_sorted q full 16 _ before sortedState hs hq
  have hpc : sortedState.pc = 5 * parentStart := hs.returned.pc
  have ha : sortedState.halted = false := hs.returned.active
  have hp := RawCandidateParentRAM.parents q full (program tail) parentStart (parent_slice tail).1 (parent_slice tail).2
    16 nodes order inverse sortedState (by decide) ht hpc ha
  have hprepared := RawCandidateParentRAM.parents_prepared q full hq (program tail) parentStart
    (parent_slice tail).1 (parent_slice tail).2 16 Metadata.orderingStart before sortedState (by decide) hs hpc ha
  dsimp only at hp hprepared
  have hrun : natRun (rawIncidenceROM q full) (program tail) parentSteps sortedState =
      natRun (rawIncidenceROM q full) (program tail) (sortedClock + parentSteps) natInitial :=
    (natRun_add _ _ _ _ _).symm
  have hcost := RawCandidateParentRAM.totalSteps_le full.length q nodes order
  have hnodes : nodes = (prepareNormalization q full).indexed.nodes.size :=
    (RawCandidateParentRAM.prepared_nodes_eq_retained q full hq).symm
  rw [hnodes] at hcost
  refine ⟨sortedClock + parentSteps, ?_, ?_⟩
  · dsimp only [parentClockBound, sortedClock, parentSteps, count]
    rw [hnodes]
    omega
  · dsimp only
    rw [← hrun]
    constructor
    · refine ⟨?_, hprepared, hp.2.2.2.2.1, hp.2.2.2.2.2, ?_⟩
      · refine ⟨order, inverse, hp.1, ?_⟩
        exact RawCandidateParentRAM.observedOrder_support_of_sorted q full 16 Metadata.orderingStart
          before sortedState hs hq
      · intro address haddress
        have hn : nodes ≤ count := ht.nodes_le
        have hcountEq : count = full.length + q + 1 := rfl
        have hprotected : RawCandidateParentRAM.ProtectedAddress 16 count nodes address := by
          refine ⟨by unfold workspaceEnd at haddress; omega, by unfold workspaceEnd at haddress; omega,
            by unfold workspaceEnd at haddress; omega, by unfold workspaceEnd at haddress; omega, Or.inr ?_⟩
          rw [RawCandidateParentRAM.parentSlot_eq]
          unfold workspaceEnd at haddress
          omega
        rw [hp.2.2.2.1 address hprotected]
        exact hzero address (by unfold workspaceEnd at haddress; omega)
    · intro index hi
      rw [hp.1.inverses index hi]
      exact inverseValuesBound_of_sorted hs index hi

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactArrays018


