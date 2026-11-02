module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010m

/-! Exclusive upper-heap frame for HD's endpoint E and everything above it.
These actual local-prefix certificates complement the leading frame. They
do not assert that the entire355-op tests loop has already been proved. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

def HighFrame {bits : Nat} (endpoint : Nat) (old fresh : BitVec bits → BitVec bits) : Prop :=
  ∀ physical, Fits bits physical → endpoint ≤ physical →
    fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)

theorem HighFrame.refl {bits : Nat} (endpoint : Nat) (heap : BitVec bits → BitVec bits) :
    HighFrame endpoint heap heap := fun _ _ _ => rfl

theorem HighFrame.trans {bits : Nat} {endpoint : Nat} {old middle fresh : BitVec bits → BitVec bits}
    (hm : HighFrame endpoint old middle) (hf : HighFrame endpoint middle fresh) : HighFrame endpoint old fresh :=
  fun physical hp he => (hf physical hp he).trans (hm physical hp he)

theorem high_address_ne {bits : Nat} (endpoint target physical : Nat)
    (he : Fits bits endpoint) (ht : target < endpoint) (hp : Fits bits physical) (hge : endpoint ≤ physical) :
    BitVec.ofNat bits physical ≠ BitVec.ofNat bits target := by
  intro hh
  have hn := (ofNat_injective_of_fit physical target hp (ht.trans he)).mp hh
  omega

theorem update_high_frame {bits : Nat} (endpoint target : Nat) (heap : BitVec bits → BitVec bits)
    (value : BitVec bits) (he : Fits bits endpoint) (ht : target < endpoint) :
    HighFrame endpoint heap (Function.update heap (BitVec.ofNat bits target) value) := by
  intro physical hp hge
  rw [Function.update_of_ne (high_address_ne endpoint target physical he ht hp hge)]

theorem scratch_lt_endpoint (workspace size q offset : Nat) (ho : offset < 16) :
    PSTRQueryLayout.header workspace size + offset < PSTRQueryLayout.endpoint workspace size q := by
  unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
  omega

theorem good_lt_endpoint (workspace size q budget : Nat) (hb : budget < q + 2) :
    PSTRQueryLayout.header workspace size + 16 + budget < PSTRQueryLayout.endpoint workspace size q := by
  unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
  omega

theorem bad_lt_endpoint (workspace size q budget : Nat) (hb : budget < q + 2) :
    PSTRQueryLayout.header workspace size + 16 + (q + 2) + budget < PSTRQueryLayout.endpoint workspace size q := by
  unfold PSTRQueryLayout.endpoint PSTRQueryLayout.childBase PSTRQueryLayout.badFlags PSTRQueryLayout.goodFlags
  omega

theorem storeSlot_prefix_high_frame {bits : Nat} (rom : PhysicalROM) (workspace size q offset : Nat)
    (source : Register) (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (he : Fits bits (PSTRQueryLayout.endpoint workspace size q)) (ho : offset < 16)
    (count : Nat) (hc : count ≤ 3) :
    HighFrame (PSTRQueryLayout.endpoint workspace size q) state.heap
      (executeOps rom ((storeSlot offset source).take count) state).heap := by
  intro physical hp hge
  exact storeSlot_prefix_frame rom offset (PSTRQueryLayout.header workspace size) source state hh _
    (high_address_ne _ _ physical he (scratch_lt_endpoint workspace size q offset ho) hp hge) count hc

theorem cached_actual_prefix_high_frame {bits origin : Nat} {containing : List PackingOp}
    (em : PA17A19RuntimeRead007.CachedEmbedded bits origin containing) (rom : PhysicalROM)
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (endpoint count : Nat) (hc : count ≤ 58) :
    HighFrame endpoint state.heap (packingRun rom containing count state).heap := by
  intro physical _ _
  exact congrFun (PA17A19RuntimeRead007.cached_actual_prefix_heap em rom state hp ha count hc) _

theorem goodStore_prefix_high_frame {bits : Nat} (rom : PhysicalROM) (workspace size q budget : Nat)
    (state : WordState bits)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hc : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 8)) = BitVec.ofNat bits budget)
    (he : Fits bits (PSTRQueryLayout.endpoint workspace size q)) (hb : budget < q + 2)
    (count : Nat) (hcount : count ≤ 10) :
    HighFrame (PSTRQueryLayout.endpoint workspace size q) state.heap
      (executeOps rom (goodStore.take count) state).heap := by
  intro physical hp hge
  have hn := high_address_ne _ _ physical he (good_lt_endpoint workspace size q budget hb) hp hge
  interval_cases count <;>
    simp +decide [goodStore, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, hc, BitVec.ofNat_add_ofNat, Function.update_of_ne hn]

theorem badStore_prefix_high_frame {bits : Nat} (rom : PhysicalROM) (workspace size q budget : Nat)
    (state : WordState bits) (hq : (rom.words .input).getD 1 0 = q)
    (hh : state.register .address = BitVec.ofNat bits (PSTRQueryLayout.header workspace size))
    (hc : state.heap (BitVec.ofNat bits (PSTRQueryLayout.header workspace size + 8)) = BitVec.ofNat bits budget)
    (he : Fits bits (PSTRQueryLayout.endpoint workspace size q)) (hb : budget < q + 2)
    (count : Nat) (hcount : count ≤ 13) :
    HighFrame (PSTRQueryLayout.endpoint workspace size q) state.heap
      (executeOps rom (budgetFinish.take count) state).heap := by
  intro physical hp hge
  have h1 : Fits bits 1 := (show 1 ≤ PSTRQueryLayout.endpoint workspace size q by
    unfold PSTRQueryLayout.endpoint; omega).trans_lt he
  have hn := high_address_ne _ _ physical he (bad_lt_endpoint workspace size q budget hb) hp hge
  change (rom.words .input)[1]?.getD 0 = q at hq
  have ha : PSTRQueryLayout.header workspace size + (q + 18) + budget =
      PSTRQueryLayout.header workspace size + 16 + (q + 2) + budget := by omega
  interval_cases count <;>
    simp +decide [budgetFinish, loadSlot, executeOps, packingExecuteOp, wordOp, wordInstruction,
      hh, hc, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, BitVec.ofNat_add_ofNat, ha,
      Function.update_of_ne hn]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
