module

public import Structure.PSTR_HD_CountIteration_036

/-! Complete actual node execution to an ACTIVE encoded exit. Inputs are
internal register facts produced by preceding code, never new ROM fields.
The full kernel's only non-workspace write is counts[B+node]. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRWordSegments PSTRCountWorkspace PSTRStaticLayout PSTRCountBounds

section Kernel

variable {bits q : Nat} (full : List (Finset (Fin q))) (command : Command) (configuration : Configuration q)
    (capWords countsBase offset origin leaf : Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (initial : WordState bits) (containing : List PackingOp)
    (hbound : origin + (programAt origin).length ≤ containing.length)
    (hcode : ∀ i (hi : i < (programAt origin).length), containing[origin + i]'(kernel_index_bound containing origin hbound i hi) = (programAt origin)[i])
    (hwords : WordsFit bits (packingCode containing)) (hpcfit : Fits bits (5 * containing.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (hN : Fits bits full.length)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 7))
    (hbase : base q full capWords bits + 16 ≤ countsBase)
    (hfit : Fits bits (countsBase + (prepareNormalization q full).indexed.nodes.size))
    (hbreg : initial.register .old = BitVec.ofNat bits countsBase)
    (horeg : initial.register .fresh = BitVec.ofNat bits offset)
    (hireg : initial.register .index = BitVec.ofNat bits node.val)
    (hlreg : initial.register .value = BitVec.ofNat bits leaf)
    (hoff : offset + ((prepareNormalization q full).indexed.children.get node).size ≤ edgeCount q full)

include hbound hcode hwords hpcfit hb hq bitmap hr hw hbase hfit hbreg hireg hlreg

theorem fetched_finish (state : WordState bits)
    (data : LoopData full configuration capWords countsBase offset node initial
      ((prepareNormalization q full).indexed.children.get node).size state)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 235))) :
    let degree := ((prepareNormalization q full).indexed.children.get node).size
    let value := if bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) = 0 then leaf
      else prefixSum full initial.heap countsBase offset degree
    let result := packingRun (callInput q full command) containing 35 state
    result.heap = Function.update state.heap (BitVec.ofNat bits (countsBase + node.val)) (BitVec.ofNat bits value) ∧
    result.register .value = BitVec.ofNat bits value ∧
    result.register .address = BitVec.ofNat bits (countsBase + node.val) ∧
    result.register .index = BitVec.ofNat bits node.val ∧ result.halted = false ∧
    result.pc = BitVec.ofNat bits (5 * (origin + 270)) ∧
    HeapRepresents q full capWords configuration result.heap := by
  dsimp only
  let rom := callInput q full command
  let workspace := base q full capWords bits
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let internal := bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)
  let total := prefixSum full initial.heap countsBase offset degree
  let value := if internal = 0 then leaf else total
  let located := executeOps rom PSTRCountWorkspace.program state
  have hl := execute_base full command configuration capWords state hb hq data.rep
  have hh : located.heap = state.heap := hl.2.2.2.2.2.1
  have h0 : located.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase := by
    rw [hh]
    simpa only [slotValue, Nat.add_zero, hbreg] using data.slots 0 (by decide)
  have h2 : located.heap (BitVec.ofNat bits (workspace + 2)) = BitVec.ofNat bits node.val := by
    rw [hh]
    simpa only [slotValue, hireg] using data.slots 2 (by decide)
  have h3 : located.heap (BitVec.ofNat bits (workspace + 3)) = BitVec.ofNat bits leaf := by
    rw [hh]
    simpa only [slotValue, hlreg] using data.slots 3 (by decide)
  have h5 : located.heap (BitVec.ofNat bits (workspace + 5)) = BitVec.ofNat bits internal := by
    rw [hh]
    simpa only [slotValue] using data.slots 5 (by decide)
  have h7 : located.heap (BitVec.ofNat bits (workspace + 7)) = BitVec.ofNat bits total := by
    rw [hh]
    simpa only [slotValue] using data.slots 7 (by decide)
  have hint : internal ≤ 1 := by unfold internal bit; split <;> omega
  have hf : Fits bits internal := by
    have hpow : 256 ≤ 2 ^ bits := (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
    unfold Fits
    omega
  have hs := execute_finishStores rom workspace countsBase node.val leaf internal total located hf hl.1 h0 h2 h3 h5 h7
  have he : (executeOps rom footer state).heap = Function.update state.heap
      (BitVec.ofNat bits (countsBase + node.val)) (BitVec.ofNat bits value) := by
    rw [footer, executeOps_append, hs.1, hh]
  have hrep : HeapRepresents q full capWords configuration (executeOps rom footer state).heap := by
    rw [he]
    exact scratch_store_represents full configuration capWords (countsBase + node.val) state.heap
      (BitVec.ofNat bits value) (by omega) hq data.rep bitmap hr
      ((show workspace + 3 ≤ workspace + 7 by omega).trans_lt hw)
      ((show countsBase + node.val ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by have hn := node.isLt; omega).trans_lt hfit)
      (by omega)
  rw [fetched_footer rom containing origin hbound hcode hwords hpcfit state hp data.active]
  refine ⟨he, ?_, ?_, ?_, ?_, ?_, hrep⟩
  · simpa only [footer, executeOps_append] using hs.2.1
  · simpa only [footer, executeOps_append] using hs.2.2.1
  · simpa only [footer, executeOps_append] using hs.2.2.2.1
  · rw [executeOps_halted, data.active]
  · rw [executeOps_pc rom footer state footer_straight, hp, footer_length, BitVec.ofNat_add_ofNat]
    congr 1

include hN horeg hoff

theorem active_node_run
    (rep : HeapRepresents q full capWords configuration initial.heap)
    (hp : initial.pc = BitVec.ofNat bits (5 * origin)) (ha : initial.halted = false) :
    let degree := ((prepareNormalization q full).indexed.children.get node).size
    let value := if bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) = 0 then leaf
      else prefixSum full initial.heap countsBase offset degree
    let result := packingRun (callInput q full command) containing (activeSteps degree) initial
    result.halted = false ∧ result.pc = BitVec.ofNat bits (5 * (origin + 270)) ∧
    result.register .value = BitVec.ofNat bits value ∧
    result.register .address = BitVec.ofNat bits (countsBase + node.val) ∧
    result.register .index = BitVec.ofNat bits node.val ∧
    HeapRepresents q full capWords configuration result.heap ∧
    (∀ child < (prepareNormalization q full).indexed.nodes.size,
      result.heap (BitVec.ofNat bits (countsBase + child)) =
        if child = node.val then BitVec.ofNat bits value else initial.heap (BitVec.ofNat bits (countsBase + child))) ∧
    (∀ physical, Fits bits physical →
      (physical < base q full capWords bits ∨ base q full capWords bits + 8 ≤ physical) →
      physical ≠ countsBase + node.val →
      result.heap (BitVec.ofNat bits physical) = initial.heap (BitVec.ofNat bits physical)) := by
  let rom := callInput q full command
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let value := if bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) = 0 then leaf
      else prefixSum full initial.heap countsBase offset degree
  let started := packingRun rom containing 121 initial
  have hs := fetched_setup_ready full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit rep hireg hp ha
  let looped := packingRun rom containing (114 * degree) started
  have hl := fetched_iterations full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq hN bitmap hr hw hbase hfit hbreg horeg hoff
    0 degree started (by omega) hs
  simp only [Nat.zero_add] at hl
  let tested := packingRun rom containing 28 looped
  have ht := fetched_test_state full command configuration capWords countsBase offset origin node initial
    containing hbound hcode hwords hpcfit hb hq degree looped hl
  have htp : tested.pc = BitVec.ofNat bits (5 * (origin + 235)) := by rw [ht.2, ite_eq_left rfl]
  have hf := fetched_finish full command configuration capWords countsBase offset origin leaf node initial
    containing hbound hcode hwords hpcfit hb hq bitmap hr hw hbase hfit hbreg hireg hlreg tested ht.1 htp
  dsimp only at hf ⊢
  rw [show activeSteps degree = 121 + (114 * degree + (28 + 35)) by unfold activeSteps; omega,
    run_add, run_add, run_add]
  refine ⟨hf.2.2.2.2.1, hf.2.2.2.2.2.1, hf.2.1, hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.2.2, ?_, ?_⟩
  · intro child hc
    rw [hf.1]
    by_cases he : child = node.val
    · rw [he, Function.update_self, ite_eq_left rfl]
    · rw [store_other _ (countsBase + node.val) (countsBase + child) _
        ((show countsBase + node.val ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by have hn := node.isLt; omega).trans_lt hfit)
        ((show countsBase + child ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by omega).trans_lt hfit) (by omega),
        ite_eq_right he]
      exact ht.1.array child hc
  · intro physical hpf hout hne
    rw [hf.1, store_other _ (countsBase + node.val) physical _
      ((show countsBase + node.val ≤ countsBase + (prepareNormalization q full).indexed.nodes.size by have hn := node.isLt; omega).trans_lt hfit)
      hpf hne]
    exact ht.1.outside physical hpf hout

end Kernel

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
