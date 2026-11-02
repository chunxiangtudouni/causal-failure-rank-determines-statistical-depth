module

public import PaperProofs.Structure.PSTR_LeafEntrySafe_091

/-! Actual access bounds for parent50 and advance32. The access-only
composition protects no extra region; the real low/high physical frames
were separately proved in025 and are not inferred from this certificate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTROuterStoreAccess

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRCountKernel PSTRCountWorkspace PSTRQueryLayout

theorem access_only {bits : Nat} (rom : PhysicalROM) (heapWords : Nat) (code : List PackingOp)
    (state : WordState bits)
    (access : ∀ count (hc : count < code.length),
      packingAccessFits rom heapWords (executeOps rom (code.take count) state) code[count]) :
    PrefixOK rom heapWords (fun _ => False) code state := by
  refine ⟨access, ?_⟩
  intro _ _ _ _ impossible
  exact impossible.elim

theorem parent_suffix_access {bits : Nat} (rom : PhysicalROM) (workspace size node heapWords : Nat)
    (state : WordState bits)
    (hw : state.register .address = BitVec.ofNat bits workspace)
    (hi : state.register .index = BitVec.ofNat bits node)
    (ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size)
    (hroom : parentsBase workspace size + node + 1 < heapWords)
    (count : Nat) (hc : count < PSTRParentCopy.suffix.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRParentCopy.suffix.take count) state)
      PSTRParentCopy.suffix[count] := by
  have he : workspace + (size + 16 + node + 1) = parentsBase workspace size + node + 1 := by
    unfold parentsBase countsBase
    omega
  change count < 9 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRParentCopy.suffix, List.take_succ_cons, List.take_zero,
      List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, hw, hi, ht, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.zero_mod, he]
    first | exact (Nat.mod_le _ _).trans_lt hroom | omega

theorem advance_access {bits : Nat} (rom : PhysicalROM) (workspace heapWords : Nat) (state : WordState bits)
    (ha : state.register .address = BitVec.ofNat bits workspace)
    (hfit : Fits bits (workspace + 15)) (hroom : workspace + 15 < heapWords)
    (count : Nat) (hc : count < PSTRCountAdvance.advance.length) :
    packingAccessFits rom heapWords (executeOps rom (PSTRCountAdvance.advance.take count) state)
      PSTRCountAdvance.advance[count] := by
  have hone : 1 < 2 ^ bits := by unfold Fits at hfit; omega
  have h4 : workspace + 4 < 2 ^ bits := (show workspace + 4 ≤ workspace + 15 by omega).trans_lt hfit
  have h14 : workspace + 14 < 2 ^ bits := (show workspace + 14 ≤ workspace + 15 by omega).trans_lt hfit
  have h15 : workspace + 4 + 11 = workspace + 15 := by omega
  have hsub : workspace + 15 - 1 = workspace + 14 := by omega
  change count < 13 at hc
  interval_cases count <;> try exact True.intro
  all_goals
    simp +decide only [PSTRCountAdvance.advance, List.take_succ_cons, List.take_zero,
      List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
      ↓reduceIte, ha, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, h15,
      Nat.mod_eq_of_lt h4, Nat.mod_eq_of_lt hfit, Nat.mod_eq_of_lt hone, hsub, Nat.mod_eq_of_lt h14]
    omega

theorem parent_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hi : state.register .index = BitVec.ofNat bits node.val)
    (hroom : base q full capWords bits < heapWords)
    (hparents : parentsBase (base q full capWords bits) (prepareNormalization q full).indexed.nodes.size +
      (prepareNormalization q full).indexed.nodes.size < heapWords) :
    PrefixOK (callInput q full command) heapWords (fun _ => False) PSTRParentCopy.program state := by
  let rom := callInput q full command
  let field : Fin 9 := ⟨1, by decide⟩
  let loaded := executeOps rom (PSTRStaticFields.program field) state
  let located := executeOps rom PSTRCountWorkspace.program loaded
  have pfield := fields_prefixOK full command configuration capWords 0 0 heapWords state field node.val hb hq rep hN
    (by simp [field, PSTRStaticLayout.chunks]) hi hroom
  have p0 := access_only rom heapWords (PSTRStaticFields.program field) state pfield.access
  have reading := PSTRStaticFields.execute_field full command configuration capWords state field node.val hb hq rep hN
    (by simp [field, PSTRStaticLayout.chunks]) hi
  have loaded_rep : HeapRepresents q full capWords configuration loaded.heap := by rw [reading.2.2.2]; exact rep
  have p1 := access_only rom heapWords PSTRCountWorkspace.program loaded
    (PSTRCountWorkspace.prefix_access full command configuration capWords heapWords loaded loaded_rep hroom hb)
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords loaded hb hq loaded_rep
  have hindex : located.register .index = BitVec.ofNat bits node.val := locating.2.2.1.trans (reading.2.2.1.trans hi)
  have ht : located.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size := by
    rw [locating.2.2.2.2.2.1, reading.2.2.2]
    simpa only [treeSize, ne_of_gt hq, ite_false] using
      (PSTRStaticHeap.headers full configuration capWords state.heap rep).1
  have p2 := access_only rom heapWords PSTRParentCopy.suffix located
    (parent_suffix_access rom (base q full capWords bits) (prepareNormalization q full).indexed.nodes.size node.val heapWords
      located locating.1 hindex ht (by have hn := node.isLt; omega))
  have joined := prefixOK_append rom heapWords (fun _ => False) (PSTRStaticFields.program field)
    (PSTRCountWorkspace.program ++ PSTRParentCopy.suffix) state p0
    (prefixOK_append rom heapWords (fun _ => False) PSTRCountWorkspace.program PSTRParentCopy.suffix loaded p1 p2)
  simpa only [PSTRParentCopy.program, List.append_assoc] using joined

theorem advance_prefixOK {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hfit : Fits bits (base q full capWords bits + 15))
    (hroom : base q full capWords bits + 15 < heapWords) :
    PrefixOK (callInput q full command) heapWords (fun _ => False) PSTRCountAdvance.program state := by
  let rom := callInput q full command
  let located := executeOps rom PSTRCountWorkspace.program state
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
  have p0 := access_only rom heapWords PSTRCountWorkspace.program state
    (PSTRCountWorkspace.prefix_access full command configuration capWords heapWords state rep (by omega) hb)
  have p1 := access_only rom heapWords PSTRCountAdvance.advance located
    (advance_access rom (base q full capWords bits) heapWords located locating.1 hfit hroom)
  exact prefixOK_append rom heapWords (fun _ => False) PSTRCountWorkspace.program PSTRCountAdvance.advance state p0 p1

theorem parent_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (whole : List PackingOp) (start : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start PSTRParentCopy.program)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hN : Fits bits full.length) (hi : state.register .index = BitVec.ofNat bits node.val)
    (hroom : base q full capWords bits < heapWords)
    (hparents : parentsBase (base q full capWords bits) (prepareNormalization q full).indexed.nodes.size +
      (prepareNormalization q full).indexed.nodes.size < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 50) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  exact (straight_prefix_safe (callInput q full command) whole PSTRParentCopy.program heapWords start (fun _ => False)
    slice.bound slice.code PSTRParentCopy.program_straight hwords hpcfit state hp ha
    (parent_prefixOK full command configuration capWords heapWords state node hb hq rep hN hi hroom hparents) clock hclock).1

theorem advance_safe {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords heapWords : Nat) (state : WordState bits)
    (whole : List PackingOp) (start : Nat)
    (slice : PSTROuterCountCode.BlockAt whole start PSTRCountAdvance.program)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hfit : Fits bits (base q full capWords bits + 15))
    (hroom : base q full capWords bits + 15 < heapWords)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 32) :
    AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  exact (straight_prefix_safe (callInput q full command) whole PSTRCountAdvance.program heapWords start (fun _ => False)
    slice.bound slice.code PSTRCountAdvance.program_straight hwords hpcfit state hp ha
    (advance_prefixOK full command configuration capWords heapWords state hb hq rep hfit hroom) clock hclock).1

end PaperProofs.Structure.LaminarTree.PSTROuterStoreAccess
