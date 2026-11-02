module

public import PaperProofs.Structure.PA17_UniformGenerator_035p

/-! The final physical HALT and original all-prefix fetch/access field.
The source is the actual dynamic RunSafe certificate, not an oracle trace. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035x

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035j PA17UniformGenerator035m PA17UniformGenerator035p

theorem actual_halt (rom : PhysicalROM) (B heapWords bits : Nat) (program : List PackingOp)
    (steps : Nat) (state : NatState) (hs : RunSafe B heapWords rom program steps state)
    (hb : Fits bits B) (hcode : WordsFit bits (packingCode program)) (hpc : Fits bits (5 * program.length))
    (hend : (natRun rom program steps state).pc = 5 * program.length) :
    packingRun rom program (steps + 1) (state.toWord bits) =
      { (natRun rom program steps state).toWord bits with halted := true } := by
  rw [packingRun_succ, actual_word_run rom B heapWords bits program steps state hs hb hcode hpc steps le_rfl]
  apply packingStep_halt rom program _ hcode ?_ (hs.final _ _ _ _ _).2.1
  change (BitVec.ofNat bits (natRun rom program steps state).pc).toNat = _
  rw [hend, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc]

theorem actual_allprefix (rom : PhysicalROM) (B heapWords bits : Nat) (program : List PackingOp)
    (steps : Nat) (state : NatState) (hs : RunSafe B heapWords rom program steps state)
    (hb : Fits bits B) (hcode : WordsFit bits (packingCode program)) (hpc : Fits bits (5 * program.length))
    (hend : (natRun rom program steps state).pc = 5 * program.length) :
    ∀ count < steps + 1,
      let fresh := packingRun rom program count (state.toWord bits)
      fresh.halted = false ∧ fresh.pc.toNat + 4 < (packingCode program).length ∧
        let fetched := physicalFetch bits (packingCode program) fresh.pc.toNat
        match PackingOp.decode fetched with
        | none => fetched = haltWords
        | some op => packingAccessFits rom heapWords fresh op := by
  intro count hc
  by_cases hbody : count < steps
  · have hh := actual_word_fetch_access rom B heapWords bits program steps state hs hb hcode hpc count hbody
    refine ⟨hh.1, hh.2.1, ?_⟩
    obtain ⟨op, hop, ha⟩ := hh.2.2
    dsimp only
    rw [hop]
    exact ha
  · have hcount : count = steps := by omega
    subst count
    rw [actual_word_run rom B heapWords bits program steps state hs hb hcode hpc steps le_rfl]
    have hpnat : ((natRun rom program steps state).toWord bits).pc.toNat = 5 * program.length := by
      change (BitVec.ofNat bits (natRun rom program steps state).pc).toNat = _
      rw [hend, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpc]
    refine ⟨(hs.final _ _ _ _ _).2.1, ?_, ?_⟩
    · rw [hpnat, packingCode_length]
      omega
    · rw [hpnat, physicalFetch_eq bits (packingCode program) (5 * program.length) hcode]
      change (match PackingOp.decode (natFetch program (5 * program.length)) with
        | none => natFetch program (5 * program.length) = haltWords
        | some op => packingAccessFits rom heapWords _ op)
      rw [natFetch_halt, decode_halt]

theorem actual_halting_output (rom : PhysicalROM) (B heapWords bits : Nat) (program : List PackingOp)
    (steps : Nat) (state : NatState) (hs : RunSafe B heapWords rom program steps state)
    (hb : Fits bits B) (hcode : WordsFit bits (packingCode program)) (hpc : Fits bits (5 * program.length))
    (hend : (natRun rom program steps state).pc = 5 * program.length)
    (address value : Nat) (ha : Fits bits address) (hv : Fits bits value)
    (hresult : (natRun rom program steps state).heap address = value) :
    (packingRun rom program (steps + 1) (state.toWord bits)).halted = true ∧
      ((packingRun rom program (steps + 1) (state.toWord bits)).heap (BitVec.ofNat bits address)).toNat = value := by
  rw [actual_halt rom B heapWords bits program steps state hs hb hcode hpc hend]
  refine ⟨rfl, ?_⟩
  change (BitVec.ofNat bits ((natRun rom program steps state).heap (BitVec.ofNat bits address).toNat)).toNat = _
  have hnat : (BitVec.ofNat bits address).toNat = address := Nat.mod_eq_of_lt ha
  rw [hnat, hresult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035x
