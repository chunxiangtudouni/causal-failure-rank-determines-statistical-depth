module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCompleteJoint

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED abstract-state physical transport for the one joint532
clock. RunFacts is supplied here only by the preceding actual producer.
These global helpers never unfold packingRun on a composed concrete state. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (actualAllocation RunFacts)
open PA06A19PrepareBankNodeBit022 (wordView)

theorem metadata_word_run_transport (q : Nat) (full : List (Finset (Fin q)))
    (containing : List PackingOp) (before : WordState (indexWidth 32 full.length q)) (clock : Nat)
    (safe : RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
      (rawIncidenceROM q full) containing clock (wordView before))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    let rom := rawIncidenceROM q full
    let after := packingRun rom containing clock before
    let native := natRun rom containing clock (wordView before)
    (∀ count ≤ clock, packingRun rom containing count before =
      (natRun rom containing count (wordView before)).toWord (indexWidth 32 full.length q)) ∧
    after.register .address = before.register .address ∧
    after.pc.toNat = native.pc ∧ after.halted = native.halted ∧
    (∀ count < clock,
      let state := packingRun rom containing count before
      state.register .address = before.register .address ∧ state.halted = false ∧
        state.pc.toNat + 4 < (packingCode containing).length ∧
        ∃ op, PackingOp.decode (fetch containing state) = some op ∧
          packingAccessFits rom (actualAllocation q full) state op) := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let H := actualAllocation q full
  let initial := wordView before
  have rfit (count : Nat) (hc : count ≤ clock) : RegistersFit bits (natRun rom containing count initial) := by
    intro reg
    exact ((safe.1.1 count hc).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have pfit (count : Nat) (hc : count ≤ clock) : Fits bits (natRun rom containing count initial).pc := by
    obtain ⟨_regs, _active, index, hi, hp⟩ := safe.1.1 count hc
    rw [hp]
    exact (Nat.mul_le_mul_left 5 hi).trans_lt hcodePC
  have word (count : Nat) (hc : count ≤ clock) :
      packingRun rom containing count before = (natRun rom containing count initial).toWord bits := by
    rw [← PA06A19PrepareBankNodeBit022.wordView_toWord before]
    exact natRun_toWord rom containing initial count hcode
      (fun k hk => ⟨rfit k (by omega), pfit k (by omega)⟩)
  dsimp only
  refine ⟨word, ?_, ?_, ?_, ?_⟩
  · rw [word _ le_rfl]
    change BitVec.ofNat bits _ = _
    rw [safe.2 _ le_rfl]
    simp only [PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [word _ le_rfl]
    change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit _ le_rfl)]
  · rw [word _ le_rfl]
    rfl
  · intro count hc
    obtain ⟨index, hi, hp, access⟩ := safe.1.2 count hc
    rw [word count hc.le]
    have pcWord : ((natRun rom containing count initial).toWord bits).pc.toNat = 5 * index := by
      change (BitVec.ofNat bits _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit count hc.le), hp]
    refine ⟨?_, (safe.1.1 count hc.le).2.1, ?_, containing[index], ?_, ?_⟩
    · change BitVec.ofNat bits _ = _
      rw [safe.2 count hc.le]
      simp only [PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [pcWord, packingCode_length]
      omega
    · change PackingOp.decode (physicalFetch bits (packingCode containing)
        ((natRun rom containing count initial).toWord bits).pc.toNat) = _
      rw [pcWord, physicalFetch_eq _ _ _ hcode]
      change PackingOp.decode (natFetch containing (5 * index)) = _
      rw [natFetch_body containing index hi, decode_encode]
    · exact physical_access_of_nat rom H _ _ (rfit count hc.le) access

/-- A physical finite frame proved on abstract states. This is applied to
the actual joint run, rather than unfolding hundreds of composed steps. -/
theorem metadata_word_frame_transport {bits : Nat} (before after : WordState bits)
    (native : NatState) (preserved : Nat → Prop)
    (hword : after = native.toWord bits)
    (frame : ∀ address, preserved address → native.heap address = (wordView before).heap address) :
    ∀ address : BitVec bits, preserved address.toNat → after.heap address = before.heap address := by
  intro address hp
  rw [hword]
  change BitVec.ofNat bits (native.heap address.toNat) = before.heap address
  rw [frame address.toNat hp]
  simp only [PA06A19PrepareBankNodeBit022.wordView, BitVec.ofNat_toNat, BitVec.setWidth_eq]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
