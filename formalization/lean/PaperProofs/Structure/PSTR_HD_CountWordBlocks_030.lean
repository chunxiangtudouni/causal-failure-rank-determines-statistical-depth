module

public import PaperProofs.Structure.PSTR_HD_CountProgram_029
import Mathlib.Tactic.IntervalCases

/-! Actual Word arithmetic of one child accumulation, the loop test and
the final node store. Mathematical sum values are proof invariants only;
the code loads a real child count and performs one real Word addition. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine AlgorithmClaims.PackedCapacityRAM
open PSTRCountWorkspace PSTRStaticHeap

theorem execute_accumulate {bits : Nat} (rom : PhysicalROM) (origin workspace countsBase child count total value : Nat)
    (state : WordState bits) (hw : Fits bits (workspace + 7))
    (hptr : state.register .address = BitVec.ofNat bits workspace)
    (hchild : state.register .value = BitVec.ofNat bits child)
    (hbase : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase)
    (hk : state.heap (BitVec.ofNat bits (workspace + 6)) = BitVec.ofNat bits count)
    (hsum : state.heap (BitVec.ofNat bits (workspace + 7)) = BitVec.ofNat bits total)
    (hvalue : state.heap (BitVec.ofNat bits (countsBase + child)) = BitVec.ofNat bits value) :
    let result := executeOps rom (accumulate origin) state
    result.heap = Function.update
      (Function.update state.heap (BitVec.ofNat bits (workspace + 7)) (BitVec.ofNat bits (total + value)))
      (BitVec.ofNat bits (workspace + 6)) (BitVec.ofNat bits (count + 1)) ∧
    result.register .value = BitVec.ofNat bits (total + value) ∧
    result.register .old = BitVec.ofNat bits (count + 1) ∧
    result.register .index = BitVec.ofNat bits workspace ∧
    result.register .flag = BitVec.ofNat bits 0 ∧
    result.register .total = BitVec.ofNat bits (5 * (origin + 121)) ∧
    result.halted = state.halted := by
  have hf6 : Fits bits (workspace + 6) := (show workspace + 6 ≤ workspace + 7 by omega).trans_lt hw
  have h67 : BitVec.ofNat bits (workspace + 6) ≠ BitVec.ofNat bits (workspace + 7) :=
    (ofNat_injective_of_fit _ _ hf6 hw).not.mpr (by omega)
  simp +decide [accumulate, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hptr, hchild, hbase, hk, hsum, hvalue, BitVec.ofNat_add_ofNat, h67]

def testOps (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .total 4)), .base (.base (.add .address .address .total)),
   .base (.base (.loadHeap .value .address)), .base (.base (.constant .total 2)),
   .base (.base (.add .address .address .total)), .base (.base (.loadHeap .old .address)),
   .base (.subtract .flag .value .old), .base (.base (.constant .total (5 * (origin + 235))))]

theorem testLead_split (origin : Nat) : testLead origin = PSTRCountWorkspace.program ++ testOps origin := rfl

theorem execute_testOps {bits : Nat} (rom : PhysicalROM) (origin workspace degree count : Nat)
    (state : WordState bits) (hd : Fits bits degree) (hkfit : Fits bits count)
    (hptr : state.register .address = BitVec.ofNat bits workspace)
    (hdegree : state.heap (BitVec.ofNat bits (workspace + 4)) = BitVec.ofNat bits degree)
    (hcount : state.heap (BitVec.ofNat bits (workspace + 6)) = BitVec.ofNat bits count) :
    let result := executeOps rom (testOps origin) state
    result.register .flag = BitVec.ofNat bits (degree - count) ∧
    result.register .total = BitVec.ofNat bits (5 * (origin + 235)) ∧
    result.heap = state.heap ∧ result.halted = state.halted := by
  have hdn : (BitVec.ofNat bits degree).toNat = degree := Nat.mod_eq_of_lt hd
  have hkn : (BitVec.ofNat bits count).toNat = count := Nat.mod_eq_of_lt hkfit
  simp +decide [testOps, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hptr, hdegree, hcount, BitVec.ofNat_add_ofNat, Nat.add_assoc, hdn, hkn]

theorem execute_test {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords origin degree count : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hd : Fits bits degree) (hkfit : Fits bits count)
    (hdegree : state.heap (BitVec.ofNat bits (base q full capWords bits + 4)) = BitVec.ofNat bits degree)
    (hcount : state.heap (BitVec.ofNat bits (base q full capWords bits + 6)) = BitVec.ofNat bits count) :
    let result := executeOps (callInput q full command) (testLead origin) state
    result.register .flag = BitVec.ofNat bits (degree - count) ∧
    result.register .total = BitVec.ofNat bits (5 * (origin + 235)) ∧
    result.heap = state.heap ∧ result.halted = state.halted := by
  rw [testLead_split, executeOps_append]
  have hl := execute_base full command configuration capWords state hb hq rep
  have ht := execute_testOps (callInput q full command) origin (base q full capWords bits) degree count
    (executeOps (callInput q full command) PSTRCountWorkspace.program state) hd hkfit hl.1
    (by rw [hl.2.2.2.2.2.1]; exact hdegree) (by rw [hl.2.2.2.2.2.1]; exact hcount)
  simpa only [hl.2.2.2.2.2.1, hl.2.2.2.2.2.2] using ht

theorem test_remaining_zero {bits : Nat} (degree count : Nat) (hk : count ≤ degree)
    (hd : Fits bits degree) :
    (BitVec.ofNat bits (degree - count)).toNat = 0 ↔ count = degree := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt hd)]
  omega

theorem execute_finishStores {bits : Nat} (rom : PhysicalROM) (workspace countsBase node leaf internal total : Nat)
    (state : WordState bits) (hf : Fits bits internal)
    (hptr : state.register .address = BitVec.ofNat bits workspace)
    (hbase : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase)
    (hnode : state.heap (BitVec.ofNat bits (workspace + 2)) = BitVec.ofNat bits node)
    (hleaf : state.heap (BitVec.ofNat bits (workspace + 3)) = BitVec.ofNat bits leaf)
    (hinternal : state.heap (BitVec.ofNat bits (workspace + 5)) = BitVec.ofNat bits internal)
    (hsum : state.heap (BitVec.ofNat bits (workspace + 7)) = BitVec.ofNat bits total) :
    let result := executeOps rom finishStores state
    result.heap = Function.update state.heap (BitVec.ofNat bits (countsBase + node))
        (BitVec.ofNat bits (if internal = 0 then leaf else total)) ∧
    result.register .value = BitVec.ofNat bits (if internal = 0 then leaf else total) ∧
    result.register .address = BitVec.ofNat bits (countsBase + node) ∧
    result.register .index = BitVec.ofNat bits node ∧ result.halted = state.halted := by
  have hfn : (BitVec.ofNat bits internal).toNat = internal := Nat.mod_eq_of_lt hf
  by_cases hz : internal = 0 <;>
    simp_all +decide [finishStores, executeOps, packingExecuteOp, wordOp, wordInstruction,
      BitVec.ofNat_add_ofNat, Nat.add_assoc]

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
