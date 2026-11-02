module

public import PaperProofs.Structure.PSTR_HD_CountRun_037
import Mathlib.Tactic.IntervalCases

/-! Memory safety of every actual prefix of the small node-kernel blocks.
Only real heap pointers and original ROM accesses occur in these statements. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine PSTRCountWorkspace

def ReadOnly : PackingOp → Prop
  | .base (.base (.storeHeap _ _)) => False
  | _ => True

theorem readOnly_heap {bits : Nat} (rom : PhysicalROM) (op : PackingOp) (state : WordState bits)
    (ho : ReadOnly op) : (packingExecuteOp rom op state).heap = state.heap := by
  cases op with
  | base op =>
    cases op with
    | base instruction => cases instruction <;> simp_all [ReadOnly, packingExecuteOp, wordOp, wordInstruction]
    | subtract target left right => rfl
  | arithmetic operation target left right => rfl
  | jumpIfZero condition target => rfl

theorem readOnly_ops_heap {bits : Nat} (rom : PhysicalROM) (ops : List PackingOp) (state : WordState bits)
    (ho : ∀ op ∈ ops, ReadOnly op) : (executeOps rom ops state).heap = state.heap := by
  induction ops generalizing state with
  | nil => rfl
  | cons op later ih =>
    exact (ih _ (fun other hother => ho other (List.mem_cons_of_mem _ hother))).trans
      (readOnly_heap rom op state (ho op List.mem_cons_self))

theorem readOnly_prefix_heap {bits : Nat} (rom : PhysicalROM) (ops : List PackingOp) (state : WordState bits)
    (ho : ∀ op ∈ ops, ReadOnly op) (count : Nat) :
    (executeOps rom (ops.take count) state).heap = state.heap :=
  readOnly_ops_heap rom _ state (fun op hop => ho op (List.mem_of_mem_take hop))

theorem locator_readOnly : ∀ op ∈ PSTRCountWorkspace.program, ReadOnly op := by
  simp [PSTRCountWorkspace.program, ReadOnly]

theorem fields_readOnly (field : Fin 9) : ∀ op ∈ PSTRStaticFields.program field, ReadOnly op := by
  simp [PSTRStaticFields.program, ReadOnly]

theorem testOps_readOnly (origin : Nat) : ∀ op ∈ testOps origin, ReadOnly op := by simp [testOps, ReadOnly]
theorem childPosition_readOnly : ∀ op ∈ childPosition, ReadOnly op := by simp [childPosition, ReadOnly]

theorem testOps_prefix_access {bits : Nat} (rom : PhysicalROM) (origin workspace heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hr : workspace + 7 < heapWords) (count : Nat) (hc : count < (testOps origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((testOps origin).take count) state) (testOps origin)[count] := by
  have hs (offset : Nat) (ho : offset ≤ 7) : (BitVec.ofNat bits (workspace + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have h4 := hs 4 (by decide)
  have h6 := hs 6 (by decide)
  change count < 8 at hc
  interval_cases count <;>
    simp_all +decide [testOps, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem childPosition_prefix_access {bits : Nat} (rom : PhysicalROM) (workspace heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hr : workspace + 7 < heapWords) (count : Nat) (hc : count < childPosition.length) :
    packingAccessFits rom heapWords (executeOps rom (childPosition.take count) state) childPosition[count] := by
  have hs (offset : Nat) (ho : offset ≤ 7) : (BitVec.ofNat bits (workspace + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have h1 := hs 1 (by decide)
  have h6 := hs 6 (by decide)
  change count < 7 at hc
  interval_cases count <;>
    simp_all +decide [childPosition, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem saveField_prefix_access {bits : Nat} (rom : PhysicalROM) (slot workspace heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hr : workspace + slot < heapWords) (count : Nat) (hc : count < (saveField slot).length) :
    packingAccessFits rom heapWords (executeOps rom ((saveField slot).take count) state) (saveField slot)[count] := by
  have hs : (BitVec.ofNat bits (workspace + slot)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hr
  change count < 3 at hc
  interval_cases count <;>
    simp_all +decide [saveField, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat]

theorem clearLoop_prefix_access {bits : Nat} (rom : PhysicalROM) (workspace heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits (workspace + 5))
    (hr : workspace + 7 < heapWords) (count : Nat) (hc : count < clearLoop.length) :
    packingAccessFits rom heapWords (executeOps rom (clearLoop.take count) state) clearLoop[count] := by
  have hs (offset : Nat) (ho : offset ≤ 7) : (BitVec.ofNat bits (workspace + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have h6 := hs 6 (by decide)
  have h7 := hs 7 (by decide)
  change count < 6 at hc
  interval_cases count <;>
    simp_all +decide [clearLoop, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat, Nat.add_assoc]

theorem accumulate_prefix_access {bits : Nat} (rom : PhysicalROM) (origin workspace countsBase child heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hc : state.register .value = BitVec.ofNat bits child)
    (hb : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase)
    (hw : workspace + 7 < heapWords) (hchild : countsBase + child < heapWords)
    (count : Nat) (hk : count < (accumulate origin).length) :
    packingAccessFits rom heapWords (executeOps rom ((accumulate origin).take count) state) (accumulate origin)[count] := by
  have hs (offset : Nat) (ho : offset ≤ 7) : (BitVec.ofNat bits (workspace + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have h0 := hs 0 (by decide)
  simp only [Nat.add_zero] at h0
  have h6 := hs 6 (by decide)
  have h7 := hs 7 (by decide)
  have hbc : (BitVec.ofNat bits (countsBase + child)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hchild
  change count < 18 at hk
  interval_cases count <;>
    simp_all +decide [accumulate, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat]

theorem finishStores_prefix_access {bits : Nat} (rom : PhysicalROM) (workspace countsBase node heapWords : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hb : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase)
    (hn : state.heap (BitVec.ofNat bits (workspace + 2)) = BitVec.ofNat bits node)
    (hw : workspace + 7 < heapWords) (hnode : countsBase + node < heapWords)
    (count : Nat) (hc : count < finishStores.length) :
    packingAccessFits rom heapWords (executeOps rom (finishStores.take count) state) finishStores[count] := by
  have hs (offset : Nat) (ho : offset ≤ 7) : (BitVec.ofNat bits (workspace + offset)).toNat < heapWords :=
    (Nat.mod_le _ _).trans_lt (by omega)
  have h0 := hs 0 (by decide)
  simp only [Nat.add_zero] at h0
  have h2 := hs 2 (by decide)
  have h3 := hs 3 (by decide)
  have h5 := hs 5 (by decide)
  have h7 := hs 7 (by decide)
  have hbn : (BitVec.ofNat bits (countsBase + node)).toNat < heapWords := (Nat.mod_le _ _).trans_lt hnode
  change count < 16 at hc
  interval_cases count <;>
    simp_all +decide [finishStores, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits, BitVec.ofNat_add_ofNat, Nat.add_assoc]

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
