module

public import Structure.PSTR_BuildLower_GlobalCapacity_085

/-! Two physical invariants on the SAME actual trace: full NEW-C capacity
and every fitted high-cache word. These are additional internal obligations
of the real compiler, not consequences of the finite C0 simulation view. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ResourceTrace
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PreparedLayout

def CacheFrame (q : Nat) (full : List (Finset (Fin q)))
    (before after : BitVec (bits q full) → BitVec (bits q full)) : Prop :=
  ∀ point, controlBase q full + 512 ≤ point → Fits (bits q full) point →
    after (BitVec.ofNat _ point) = before (BitVec.ofNat _ point)

theorem CacheFrame.refl (q : Nat) (full : List (Finset (Fin q)))
    (heap : BitVec (bits q full) → BitVec (bits q full)) : CacheFrame q full heap heap := by
  intro point hp hf
  rfl

theorem CacheFrame.trans {q : Nat} {full : List (Finset (Fin q))}
    {first middle last : BitVec (bits q full) → BitVec (bits q full)}
    (later : CacheFrame q full middle last) (earlier : CacheFrame q full first middle) :
    CacheFrame q full first last := by
  intro point hp hf
  exact (later point hp hf).trans (earlier point hp hf)

def Keeps (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (whole : List PackingOp) (state : WordState (bits q full)) (count : Nat) : Prop :=
  ∀ clock ≤ count, GlobalCapacity.Bounded q full (packingRun physical whole clock state).heap ∧
    CacheFrame q full state.heap (packingRun physical whole clock state).heap

theorem keeps_zero (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (whole : List PackingOp) (state : WordState (bits q full)) (bounded : GlobalCapacity.Bounded q full state.heap) :
    Keeps q full physical whole state 0 := by
  intro clock hc
  have he : clock = 0 := by omega
  subst clock
  exact ⟨bounded, CacheFrame.refl q full state.heap⟩

theorem keeps_add (q : Nat) (full : List (Finset (Fin q))) (physical : PhysicalROM)
    (whole : List PackingOp) (state : WordState (bits q full)) (first second : Nat)
    (before : Keeps q full physical whole state first)
    (after : Keeps q full physical whole (packingRun physical whole first state) second) :
    Keeps q full physical whole state (first + second) := by
  intro clock hc
  by_cases he : clock ≤ first
  · exact before clock he
  · have split : clock = first + (clock - first) := by omega
    have tail := after (clock - first) (by omega)
    rw [split, PSTRWordSegments.run_add]
    exact ⟨tail.1, CacheFrame.trans tail.2 (before first le_rfl).2⟩

theorem bank_range_cache (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (block : List PackingOp) (lo hi : Nat) (hhi : hi ≤ 512)
    (frame : BankRangeFrame (bits := bits q full) physical block lo hi) (state : WordState (bits q full))
    (hbase : state.register .address = BitVec.ofNat _ (controlBase q full)) (count : Nat) :
    CacheFrame q full state.heap (executeOps physical (block.take count) state).heap := by
  intro point hp hf
  apply frame.2
  intro changed hlo hlast
  rw [hbase, BitVec.ofNat_add_ofNat]
  exact word_address_ne hf (bank_offset_fits q full hq changed (by omega)) (by omega)

theorem bank_actual_keeps (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (physical : PhysicalROM) (block : List PackingOp) (lo hi : Nat) (horder : lo ≤ hi) (hhi : hi ≤ 512)
    (frame : BankRangeFrame (bits := bits q full) physical block lo hi) (straight : StraightProgram block)
    (state : WordState (bits q full)) (hbase : state.register .address = BitVec.ofNat _ (controlBase q full))
    (bounded : GlobalCapacity.Bounded q full state.heap) (left right : List PackingOp)
    (hpc : state.pc = BitVec.ofNat _ (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ block ++ right)))
    (hpcfit : Fits (bits q full) (5 * (left ++ block ++ right).length)) :
    Keeps q full physical (left ++ block ++ right) state block.length := by
  intro clock hc
  refine ⟨GlobalCapacity.bank_actual_prefix q full hq physical block lo hi horder hhi frame straight
    state hbase bounded left right hpc ha hcode hpcfit clock hc, ?_⟩
  rw [SourceRep.straight_prefix physical left block right state straight hcode hpcfit hpc ha clock hc]
  exact bank_range_cache q full hq physical block lo hi hhi frame state hbase clock

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ResourceTrace
