module

public import Structure.PSTR_HD_CountMemoryBlocks_038

/-! Every actual scratch-store prefix leaves the original metadata/capacity
prefix and the caller's W8..W15 words unchanged. The only later exception is
the single final counts[B+node] store. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRCountKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine AlgorithmClaims.PackedCapacityRAM PSTRCountWorkspace

theorem outside_word_ne {bits : Nat} (workspace physical offset : Nat)
    (hw : Fits bits (workspace + 7)) (hp : Fits bits physical) (ho : offset ≤ 7)
    (hout : physical < workspace ∨ workspace + 8 ≤ physical) :
    BitVec.ofNat bits physical ≠ BitVec.ofNat bits (workspace + offset) :=
  (ofNat_injective_of_fit physical (workspace + offset) hp
    ((show workspace + offset ≤ workspace + 7 by omega).trans_lt hw)).not.mpr (by omega)

theorem spill_prefix_outside {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits workspace)
    (hw : Fits bits (workspace + 7)) (physical : Nat) (hf : Fits bits physical)
    (hout : physical < workspace ∨ workspace + 8 ≤ physical)
    (count : Nat) (hc : count ≤ spillProgram.length) :
    (executeOps rom (spillProgram.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hn (offset : Nat) (ho : offset ≤ 7) := outside_word_ne workspace physical offset hw hf ho hout
  have h0 : BitVec.ofNat bits physical ≠ BitVec.ofNat bits workspace := by simpa using hn 0 (by decide)
  change count ≤ 8 at hc
  interval_cases count <;>
    simp (disch := omega) [spillProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, BitVec.ofNat_add_ofNat, Nat.add_assoc, Function.update_apply, hn]

theorem saveField_prefix_outside {bits : Nat} (rom : PhysicalROM) (slot workspace : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits workspace)
    (hw : Fits bits (workspace + 7)) (hslot : slot ≤ 7) (physical : Nat) (hf : Fits bits physical)
    (hout : physical < workspace ∨ workspace + 8 ≤ physical)
    (count : Nat) (hc : count ≤ (saveField slot).length) :
    (executeOps rom ((saveField slot).take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hn := outside_word_ne workspace physical slot hw hf hslot hout
  change count ≤ 3 at hc
  interval_cases count <;>
    simp [saveField, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, BitVec.ofNat_add_ofNat, hn]

theorem clearLoop_prefix_outside {bits : Nat} (rom : PhysicalROM) (workspace : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits (workspace + 5))
    (hw : Fits bits (workspace + 7)) (physical : Nat) (hf : Fits bits physical)
    (hout : physical < workspace ∨ workspace + 8 ≤ physical)
    (count : Nat) (hc : count ≤ clearLoop.length) :
    (executeOps rom (clearLoop.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hn (offset : Nat) (ho : offset ≤ 7) := outside_word_ne workspace physical offset hw hf ho hout
  change count ≤ 6 at hc
  interval_cases count <;>
    simp (disch := omega) [clearLoop, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, BitVec.ofNat_add_ofNat, Nat.add_assoc, Function.update_apply, hn]

theorem accumulate_prefix_outside {bits : Nat} (rom : PhysicalROM) (origin workspace : Nat) (state : WordState bits)
    (hp : state.register .address = BitVec.ofNat bits workspace)
    (hw : Fits bits (workspace + 7)) (physical : Nat) (hf : Fits bits physical)
    (hout : physical < workspace ∨ workspace + 8 ≤ physical)
    (count : Nat) (hc : count ≤ (accumulate origin).length) :
    (executeOps rom ((accumulate origin).take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hn (offset : Nat) (ho : offset ≤ 7) := outside_word_ne workspace physical offset hw hf ho hout
  change count ≤ 18 at hc
  interval_cases count <;>
    simp (disch := omega) [accumulate, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, BitVec.ofNat_add_ofNat, Function.update_apply, hn]

theorem finishStores_prefix_other {bits : Nat} (rom : PhysicalROM) (workspace countsBase node : Nat)
    (state : WordState bits) (hp : state.register .address = BitVec.ofNat bits workspace)
    (hb : state.heap (BitVec.ofNat bits workspace) = BitVec.ofNat bits countsBase)
    (hn : state.heap (BitVec.ofNat bits (workspace + 2)) = BitVec.ofNat bits node)
    (hstore : Fits bits (countsBase + node)) (physical : Nat) (hf : Fits bits physical)
    (hne : physical ≠ countsBase + node)
    (count : Nat) (hc : count ≤ finishStores.length) :
    (executeOps rom (finishStores.take count) state).heap (BitVec.ofNat bits physical) =
      state.heap (BitVec.ofNat bits physical) := by
  have hword := (ofNat_injective_of_fit physical (countsBase + node) hf hstore).not.mpr hne
  change count ≤ 16 at hc
  interval_cases count <;>
    simp [finishStores, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hp, hb, hn, BitVec.ofNat_add_ofNat, Nat.add_assoc, hword]

end PaperProofs.Structure.LaminarTree.PSTRCountKernel
