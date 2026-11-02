module

public import PaperProofs.Structure.PSTR_HD_CountSetup_031

/-! A real child iteration loads its child ID from ORIGINAL cached metadata,
then its previous count from physical scratch. It writes one real addition
to W7 and increments the real loop counter in W6. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine AlgorithmClaims.PackedCapacityRAM
open PSTRCountWorkspace PSTRStaticHeap PSTRStaticLayout PSTRCountBounds

theorem execute_childPosition {bits : Nat} (rom : PhysicalROM) (workspace offset count : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (ho : state.heap (BitVec.ofNat bits (workspace + 1)) = BitVec.ofNat bits offset)
    (hk : state.heap (BitVec.ofNat bits (workspace + 6)) = BitVec.ofNat bits count) :
    (executeOps rom childPosition state).register .index = BitVec.ofNat bits (offset + count) ∧
      (executeOps rom childPosition state).heap = state.heap := by
  simp +decide [childPosition, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, ho, hk, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem execute_bodyLead {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords origin countsBase offset count total : Nat)
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap) (hN : Fits bits full.length)
    (hw : Fits bits (base q full capWords bits + 7)) (ho : offset + count < edgeCount q full)
    (hbase : state.heap (BitVec.ofNat bits (base q full capWords bits)) = BitVec.ofNat bits countsBase)
    (hoffset : state.heap (BitVec.ofNat bits (base q full capWords bits + 1)) = BitVec.ofNat bits offset)
    (hcount : state.heap (BitVec.ofNat bits (base q full capWords bits + 6)) = BitVec.ofNat bits count)
    (hsum : state.heap (BitVec.ofNat bits (base q full capWords bits + 7)) = BitVec.ofNat bits total) :
    let child := (PSTRStaticLayout.childWords q full).getD (offset + count) 0
    let actualChildCount := (state.heap (BitVec.ofNat bits (countsBase + child))).toNat
    let result := executeOps (callInput q full command) (bodyLead origin) state
    result.heap = Function.update
      (Function.update state.heap (BitVec.ofNat bits (base q full capWords bits + 7))
        (BitVec.ofNat bits (total + actualChildCount)))
      (BitVec.ofNat bits (base q full capWords bits + 6)) (BitVec.ofNat bits (count + 1)) ∧
    result.register .value = BitVec.ofNat bits (total + actualChildCount) ∧
    result.register .flag = BitVec.ofNat bits 0 ∧
    result.register .total = BitVec.ofNat bits (5 * (origin + 121)) ∧ result.halted = state.halted := by
  let rom := callInput q full command
  let workspace := base q full capWords bits
  let child := (PSTRStaticLayout.childWords q full).getD (offset + count) 0
  let actualChildCount := (state.heap (BitVec.ofNat bits (countsBase + child))).toNat
  let s0 := executeOps rom PSTRCountWorkspace.program state
  have h0 := execute_base full command configuration capWords state hb hq rep
  let s1 := executeOps rom childPosition s0
  have h1 := execute_childPosition rom workspace offset count s0 h0.1
    (by rw [h0.2.2.2.2.2.1]; exact hoffset) (by rw [h0.2.2.2.2.2.1]; exact hcount)
  have r1 : HeapRepresents q full capWords configuration s1.heap := by
    rw [h1.2, h0.2.2.2.2.2.1]
    exact rep
  let s2 := executeOps rom (PSTRStaticFields.program ⟨3, by decide⟩) s1
  have h2 := PSTRStaticFields.execute_field full command configuration capWords s1 ⟨3, by decide⟩
    (offset + count) hb hq r1 hN ho h1.1
  have c2 : s2.register .value = BitVec.ofNat bits child := by
    have hv := h2.1
    change s2.register .value = BitVec.ofNat bits ((PSTRStaticLayout.childWords q full)[offset + count]) at hv
    change s2.register .value = BitVec.ofNat bits ((PSTRStaticLayout.childWords q full).getD (offset + count) 0)
    rw [List.getD_eq_getElem _ _ ho]
    exact hv
  have r2 : HeapRepresents q full capWords configuration s2.heap := by rw [h2.2.2.2]; exact r1
  let s3 := executeOps rom PSTRCountWorkspace.program s2
  have h3 := execute_base full command configuration capWords s2 hb hq r2
  have hh : s3.heap = state.heap := h3.2.2.2.2.2.1.trans (h2.2.2.2.trans (h1.2.trans h0.2.2.2.2.2.1))
  have h4 := execute_accumulate rom origin workspace countsBase child count total actualChildCount s3 hw h3.1
    (h3.2.1.trans c2) (by rw [hh]; exact hbase) (by rw [hh]; exact hcount) (by rw [hh]; exact hsum) (by
      rw [hh]
      simp only [actualChildCount, BitVec.ofNat_toNat, BitVec.setWidth_eq])
  simp only [bodyLead, executeOps_append]
  change (executeOps rom (accumulate origin) s3).heap = _ ∧ _
  exact ⟨by simpa only [hh] using h4.1, h4.2.1, h4.2.2.2.2.1,
    h4.2.2.2.2.2.1, by simp only [executeOps_halted]⟩

theorem slots_after_accumulate {bits : Nat} (workspace degree internal count total childValue : Nat)
    (initial : WordState bits) (heap : BitVec bits → BitVec bits)
    (hw : Fits bits (workspace + 7)) (hs : HasSlots workspace degree internal count total initial heap) :
    HasSlots workspace degree internal (count + 1) (total + childValue) initial
      (Function.update
        (Function.update heap (BitVec.ofNat bits (workspace + 7)) (BitVec.ofNat bits (total + childValue)))
        (BitVec.ofNat bits (workspace + 6)) (BitVec.ofNat bits (count + 1))) := by
  have he (a b : Nat) (ha : a ≤ workspace + 7) (hb : b ≤ workspace + 7) :
      BitVec.ofNat bits a = BitVec.ofNat bits b ↔ a = b :=
    ofNat_injective_of_fit a b (ha.trans_lt hw) (hb.trans_lt hw)
  intro slot hslot
  have hv := hs slot hslot
  interval_cases slot <;>
    simp (disch := omega) [Function.update_apply, he, slotValue] at hv ⊢ <;> assumption

theorem child_id_lt {q : Nat} (full : List (Finset (Fin q))) (position : Nat)
    (hp : position < edgeCount q full) :
    (PSTRStaticLayout.childWords q full).getD position 0 < (prepareNormalization q full).indexed.nodes.size := by
  let value := (PSTRStaticLayout.childWords q full).getD position 0
  change value < _
  have hm : value ∈ PSTRStaticLayout.childWords q full := by
    change (PSTRStaticLayout.childWords q full).getD position 0 ∈ _
    rw [List.getD_eq_getElem _ _ hp]
    exact List.getElem_mem hp
  change value ∈ (List.finRange (prepareNormalization q full).indexed.nodes.size).flatMap
    (fun parent => ((prepareNormalization q full).indexed.children.get parent).toList.map Fin.val) at hm
  obtain ⟨parent, _hparent, hm⟩ := List.mem_flatMap.mp hm
  obtain ⟨child, _hchild, he⟩ := List.mem_map.mp hm
  exact he ▸ child.isLt

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
