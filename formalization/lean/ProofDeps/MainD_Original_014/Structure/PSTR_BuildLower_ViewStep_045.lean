module

public import Structure.PSTR_BuildLower_ConcreteWrite_033
public import Structure.PA06_A19Prepare_PackedView013

/-! Concrete fetched ports consume the original frozen two-cutoff SAME-heap
view. Logical C0 metadata stays ordinary even when physical C is larger.
The actual writer's physical replacement is identified with the proved view
update; no generated code is treated as if it had executed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ViewStep
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
variable {bits : Nat}

private theorem target_eq (state : WordState bits) (pointer : Register) (C0 indexBase a : Nat)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase) :
    Ordinary.targetAddress state pointer = BitVec.ofNat bits (indexBase + (a - C0)) := by
  have hb : state.heap (state.register .address + BitVec.ofNat bits 6) = BitVec.ofNat bits indexBase := by
    rw [← hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  simp only [Ordinary.targetAddress, hp, hc, hb, BitVec.ofNat_add_ofNat]

theorem readView_eq (q C0 C indexBase a : Nat) (state : WordState bits) (pointer : Register)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase) :
    ConcreteHeap.readView q C state pointer = PA06A19PreparePackedView013.view q C0 C indexBase state.heap a := by
  rw [ConcreteHeap.readView, hp, hc, target_eq state pointer C0 indexBase a hp hc hi]
  rfl

theorem physicalWrite_eq (q a : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    PA06A19PrepareRuntimePacked016.physicalWrite (CapacityBits.width q) (a * CapacityBits.width q) value heap =
      PA06A19PreparePackedView013.packedStore q a value heap := by
  simp only [PA06A19PrepareRuntimePacked016.physicalWrite, PA06A19PreparePackedView013.packedStore,
    Nat.add_comm, Nat.add_left_comm]

theorem writeView_update (q C0 C indexBase indexWords a : Nat) (state : WordState bits) (pointer : Register)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase)
    (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits) (hC : C0 ≤ C)
    (hregion : Fits bits (C * CapacityBits.width q))
    (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hend : Fits bits (indexBase + indexWords)) (had : a < C0 + indexWords)
    (hnext : a < C0 → Fits bits (a * CapacityBits.width q / bits + 1))
    (hv : a < C0 → (state.register .value).toNat ≤ q)
    (other : Nat) (ho : other < C0 + indexWords) :
    PA06A19PreparePackedView013.view q C0 C indexBase (ConcreteHeap.writeViewHeap q state pointer) other =
      (Function.update (PA06A19PreparePackedView013.view q C0 C indexBase state.heap) a (state.register .value).toNat) other := by
  by_cases ha : a < C0
  · have hn : ¬DispatchRun.ordinaryCase pointer state := by
      change ¬(state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat
      rw [hc, hp]
      omega
    rw [ConcreteHeap.writeViewHeap, ite_eq_right hn, hp, physicalWrite_eq]
    exact PA06A19PreparePackedView013.view_packedStore q C0 C indexBase indexWords a
      (state.register .value) state.heap hb hw hC ha (hnext ha) hregion (hv ha) hbase hend other ho
  · have hg : DispatchRun.ordinaryCase pointer state := by
      change (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat
      rw [hc, hp]
      omega
    rw [ConcreteHeap.writeViewHeap, ite_eq_left hg, target_eq state pointer C0 indexBase a hp hc hi]
    exact PA06A19PreparePackedView013.view_indexStore q C0 C indexBase indexWords a
      (state.register .value) state.heap hb hC hregion hbase (by omega) had hend other ho

theorem read_call_view (q C0 C indexBase a : Nat) (rom : PhysicalROM) (left right : List PackingOp)
    (pointer : Register) (state : WordState bits)
    (hp : (Ordinary.pointerValue state pointer).toNat = a)
    (hc : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat = C0)
    (hi : (state.heap (state.register .address + BitVec.ofNat bits 6)).toNat = indexBase)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap) (hb : 0 < bits)
    (hw : CapacityBits.width q ≤ bits) (hC : C0 ≤ C)
    (hscale : a < C0 → Fits bits (a * CapacityBits.width q))
    (hcode : WordsFit bits (packingCode (left ++ ConcreteHeap.read left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ ConcreteHeap.read left.length pointer ++ right).length))
    (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false) :
    let count := DispatchRun.steps PA06A19PrepareBankPacked021.read (Ordinary.read pointer) pointer state
    count ≤ 45 ∧
      ((packingRun rom (left ++ ConcreteHeap.read left.length pointer ++ right) count state).register .value).toNat =
        PA06A19PreparePackedView013.view q C0 C indexBase state.heap a := by
  have actual := ConcreteHeap.read_call_value q C rom left right pointer state hh hb hw
    (by rwa [hc]) (by simpa only [hp, hc] using hscale) hcode hpcfit hpc ha
  exact ⟨actual.1, actual.2.trans (readView_eq q C0 C indexBase a state pointer hp hc hi)⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ViewStep
