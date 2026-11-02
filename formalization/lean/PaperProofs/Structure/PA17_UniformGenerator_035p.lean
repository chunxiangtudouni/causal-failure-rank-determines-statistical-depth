module

public import PaperProofs.Structure.PA17_UniformGenerator_035m

/-! Transport of actual dynamic compiler safety to original physical fetch,
without a host trace, decoded output table, or a changed instruction set. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035p

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety PA17UniformGenerator035j PA17UniformGenerator035m

theorem registersFit_of_le (B bits : Nat) (state : NatState) (hb : Fits bits B) (hr : RegistersLE B state) :
    RegistersFit bits state := fun register => lt_of_le_of_lt (hr register) hb

theorem actual_word_run (rom : PhysicalROM) (B heapWords bits : Nat) (program : List PackingOp)
    (steps : Nat) (state : NatState) (hs : RunSafe B heapWords rom program steps state)
    (hb : Fits bits B) (hcode : WordsFit bits (packingCode program)) (hpc : Fits bits (5 * program.length))
    (count : Nat) (hc : count ≤ steps) :
    packingRun rom program count (state.toWord bits) = (natRun rom program count state).toWord bits := by
  apply natRun_toWord rom program state count hcode
  intro index hi
  have hh := hs.1 index (by omega)
  refine ⟨registersFit_of_le B bits _ hb hh.1, ?_⟩
  obtain ⟨position, hp, he⟩ := hh.2.2
  rw [he]
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 5 hp) hpc

theorem actual_word_fetch_access (rom : PhysicalROM) (B heapWords bits : Nat) (program : List PackingOp)
    (steps : Nat) (state : NatState) (hs : RunSafe B heapWords rom program steps state)
    (hb : Fits bits B) (hcode : WordsFit bits (packingCode program)) (hpc : Fits bits (5 * program.length))
    (count : Nat) (hc : count < steps) :
    let fresh := packingRun rom program count (state.toWord bits)
    fresh.halted = false ∧ fresh.pc.toNat + 4 < (packingCode program).length ∧
      let fetched := physicalFetch bits (packingCode program) fresh.pc.toNat
      ∃ op, PackingOp.decode fetched = some op ∧ packingAccessFits rom heapWords fresh op := by
  rw [actual_word_run rom B heapWords bits program steps state hs hb hcode hpc count hc.le]
  have hsnum := hs.1 count hc.le
  obtain ⟨index, hi, hindexpc, haccess⟩ := hs.2 count hc
  have hpfit : Fits bits (natRun rom program count state).pc := by
    rw [hindexpc]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left 5 hi.le) hpc
  have hpnat : ((natRun rom program count state).toWord bits).pc.toNat = 5 * index := by
    change (BitVec.ofNat bits (natRun rom program count state).pc).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpfit, hindexpc]
  refine ⟨hsnum.2.1, ?_, ?_⟩
  · rw [hpnat, packingCode_length]
    omega
  · rw [hpnat, physicalFetch_eq bits (packingCode program) (5 * index) hcode]
    change ∃ op, PackingOp.decode (natFetch program (5 * index)) = some op ∧ _
    rw [natFetch_body program index hi, decode_encode]
    exact ⟨program[index], rfl, physical_access_of_nat rom heapWords _ _ (registersFit_of_le B bits _ hb hsnum.1) haccess⟩

theorem actual_word_output (rom : PhysicalROM) (B heapWords bits : Nat) (program : List PackingOp)
    (steps : Nat) (state : NatState) (hs : RunSafe B heapWords rom program steps state)
    (hb : Fits bits B) (hcode : WordsFit bits (packingCode program)) (hpc : Fits bits (5 * program.length))
    (address value : Nat) (ha : Fits bits address) (hv : Fits bits value)
    (hresult : (natRun rom program steps state).heap address = value) :
    ((packingRun rom program steps (state.toWord bits)).heap (BitVec.ofNat bits address)).toNat = value := by
  rw [actual_word_run rom B heapWords bits program steps state hs hb hcode hpc steps le_rfl]
  change (BitVec.ofNat bits ((natRun rom program steps state).heap (BitVec.ofNat bits address).toNat)).toNat = _
  have hanat : (BitVec.ofNat bits address).toNat = address := Nat.mod_eq_of_lt ha
  rw [hanat, hresult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv]

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035p
