module

public import Structure.PA06_A19Prepare_CompactArrays018
public import Structure.PA06_A19Prepare_ROM_001
public import PaperProofs.Structure.RawCandidateRetentionWordChunks
public import PaperProofs.Structure.RawCandidatePairScanWord
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Real PairScan scalar-piece core for the compact retention Word line.
Only the five SHORT existing ISA-piece bounds are generalized to full
width32. Original Nat path/segment proofs are reused without rebuilding
PairScan or retention semantics. Every access of these pieces is within
the first eight heap words, hence within008's linear allocation. This
module does not yet assert safety of the two candidate kernels or of the
whole125-op PairScan loop, nor the398-op retention loop. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open RawCandidatePairScan (programAt initBlock leftArguments rightArguments updateLead update)
open RawCandidatePairScanWord (Chunk chunkCode chunkOffset chunkLength chunkLead chunkLast
  chunk_length chunk_span chunk_split chunk_lead_length chunk_lead_noJump chunk_slice
  chunk_run_prefix chunk_run)

abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit

/-- The old polynomial value bound is used ONLY for logarithmic word
values, never as an address or workspace allocation. -/
private theorem small_fits (N q value : Nat) (hv : value ≤ N * q + N + q + 640) :
    Fits (indexWidth 32 N q) value :=
  PA06A19PrepareCompactWord008.fits_width32_of_width16 N q value
    (hv.trans_lt (fits_checker_register_bound N q))

theorem init_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state) (count : Nat) (hc : count ≤ 16) :
    RegistersFit (indexWidth 32 full.length q) (runOps (rawIncidenceROM q full) (initBlock.take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [initBlock, setCell, storeCell, runOps, natExecuteOp, Op.execute, Instruction.execute, raw_header_q]
  all_goals first | exact hf _ | apply small_fits; omega

theorem test_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (h0 : state.heap 0 ≤ q) (h3 : state.heap 3 ≤ q)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ 7) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((testCell 0 3 (start + 125)).take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [testCell, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | exact hend | apply small_fits; omega

theorem leftArgs_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (h1 : state.heap 1 < full.length + q + 1) (h3 : state.heap 3 ≤ q)
    (count : Nat) (hc : count ≤ 4) :
    RegistersFit (indexWidth 32 full.length q) (runOps (rawIncidenceROM q full) (leftArguments.take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [leftArguments, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | apply small_fits; omega

theorem rightArgs_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (h2 : state.heap 2 < full.length + q + 1) (h3 : state.heap 3 ≤ q)
    (count : Nat) (hc : count ≤ 6) :
    RegistersFit (indexWidth 32 full.length q) (runOps (rawIncidenceROM q full) (rightArguments.take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [rightArguments, storeCell, loadCell, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | apply small_fits; omega

theorem update_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (state : NatState)
    (hf : RegistersFit (indexWidth 32 full.length q) state)
    (h3 : state.heap 3 < q) (h4 : state.heap 4 ≤ state.heap 3)
    (h5 : state.heap 5 ≤ state.heap 3) (h6 : state.heap 6 ≤ state.heap 3)
    (h7 : state.heap 7 ≤ 1) (hvalue : state.register .value ≤ 1)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ 28) :
    RegistersFit (indexWidth 32 full.length q) (runOps (rawIncidenceROM q full) ((update start).take count) state) := by
  have hloop : Fits (indexWidth 32 full.length q) (5 * (start + 16)) := lt_of_le_of_lt (by omega) hend
  have hmin : min (state.heap 7) (state.register .value) ≤ 1 := (Nat.min_le_left _ _).trans h7
  have hleft : state.heap 7 - state.register .value ≤ 1 := (Nat.sub_le _ _).trans h7
  have hright : state.register .value - state.heap 7 ≤ 1 := (Nat.sub_le _ _).trans hvalue
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [update, updateLead, loadCell, addWitness, incrementCell, storeCell, jumpTo,
      runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact hf _ | exact hloop | apply small_fits; omega

/-- These five pieces actually access only heap0..7. No former large
workspace address or allocation is retained by this statement. -/
theorem chunk_prefix_accessFits (q : Nat) (full : List (Finset (Fin q))) (start : Nat) (chunk : Chunk)
    (state : NatState) (count : Nat) (hc : count < chunkLength chunk) :
    NatAccessFits (rawIncidenceROM q full) 8
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state)
      ((chunkCode start chunk).getD count RawCandidatePairScanWord.paddingOp) := by
  cases chunk
  all_goals dsimp only [chunkLength] at hc
  all_goals interval_cases count
  all_goals
    simp [chunkCode, initBlock, testCell, leftArguments, rightArguments, update, updateLead,
      setCell, storeCell, loadCell, addWitness, incrementCell, jumpTo, runOps, natExecuteOp,
      Op.execute, Instruction.execute, NatAccessFits, AccessFits, rawIncidenceROM, PhysicalROM.words]

/-- Exactly the ordinary source cells needed by each concrete short piece.
These do not contain execution safety or a candidate-query answer. -/
def Needs (q : Nat) (full : List (Finset (Fin q))) : Chunk → NatState → Prop
  | .init, _ => True
  | .test, state => state.heap 0 ≤ q ∧ state.heap 3 ≤ q
  | .leftArgs, state => state.heap 1 < full.length + q + 1 ∧ state.heap 3 ≤ q
  | .rightArgs, state => state.heap 2 < full.length + q + 1 ∧ state.heap 3 ≤ q
  | .update, state => state.heap 3 < q ∧ state.heap 4 ≤ state.heap 3 ∧
      state.heap 5 ≤ state.heap 3 ∧ state.heap 6 ≤ state.heap 3 ∧
      state.heap 7 ≤ 1 ∧ state.register .value ≤ 1

theorem chunk_prefix_registersFit (q : Nat) (full : List (Finset (Fin q))) (start : Nat)
    (chunk : Chunk) (state : NatState) (hfit : RegistersFit (indexWidth 32 full.length q) state)
    (needs : Needs q full chunk state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    RegistersFit (indexWidth 32 full.length q)
      (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state) := by
  cases chunk with
  | init => exact init_prefix_registersFit q full state hfit count hc
  | test => exact test_prefix_registersFit q full start state hfit needs.1 needs.2 hend count hc
  | leftArgs => exact leftArgs_prefix_registersFit q full state hfit needs.1 needs.2 count hc
  | rightArgs => exact rightArgs_prefix_registersFit q full state hfit needs.1 needs.2 count hc
  | update =>
    exact update_prefix_registersFit q full start state hfit needs.1 needs.2.1 needs.2.2.1
      needs.2.2.2.1 needs.2.2.2.2.1 needs.2.2.2.2.2 hend count hc

def SafePoint (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
    (state : NatState) : Prop :=
  RegistersFit (indexWidth 32 full.length q) state ∧
    ∃ offset < 125, state.pc = 5 * (start + offset) ∧ state.halted = false ∧
      ∃ op, PackingOp.decode (natFetch containing state.pc) = some op ∧
        NatAccessFits (rawIncidenceROM q full) 8 state op

theorem SafePoint.pcFits {q : Nat} {full : List (Finset (Fin q))} {containing : List PackingOp} {start : Nat}
    {state : NatState} (point : SafePoint q full containing start state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125))) :
    Fits (indexWidth 32 full.length q) state.pc := by
  obtain ⟨offset, hoff, pc, _⟩ := point.2
  rw [pc]
  exact lt_of_le_of_lt (by omega) hend

private theorem chunk_pure_prefix_pc (q : Nat) (full : List (Finset (Fin q)))
    (start : Nat) (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (count : Nat) (hc : count < chunkLength chunk) :
    (runOps (rawIncidenceROM q full) ((chunkCode start chunk).take count) state).pc =
      5 * (start + (chunkOffset chunk + count)) := by
  have hlen := chunk_lead_length start chunk
  have hc' : count ≤ (chunkLead start chunk).length := by omega
  rw [chunk_split start chunk, List.take_append_of_le_length hc',
    runOps_pc _ _ _ (fun op hop => chunk_lead_noJump start chunk op (List.mem_of_mem_take hop)),
    List.length_take_of_le hc', hpc]
  omega

section Linked

variable (q : Nat) (full : List (Finset (Fin q))) (containing : List PackingOp) (start : Nat)
  (hbound : start + 125 ≤ containing.length)
  (hcode : ∀ position < 125, containing.getD (start + position) RawCandidatePairScanWord.paddingOp =
    (programAt start).getD position RawCandidatePairScanWord.paddingOp)

include hbound hcode

/-- Actual encoded run and every strict prefix, from source-cell needs.
The existing generic Nat segment theorem includes the true final branch. -/
theorem chunk_safe (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hfit : RegistersFit (indexWidth 32 full.length q) state) (needs : Needs q full chunk state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125))) :
    PrefixSafe (SafePoint q full containing start) (rawIncidenceROM q full) containing state (chunkLength chunk) ∧
      RegistersFit (indexWidth 32 full.length q)
        (natRun (rawIncidenceROM q full) containing (chunkLength chunk) state) := by
  constructor
  · intro count hc
    rw [chunk_run_prefix q full containing start hbound hcode chunk state hpc ha count hc.le]
    have hspan := chunk_span chunk
    have hs := chunk_slice containing start hbound hcode chunk
    have hp := chunk_pure_prefix_pc q full start chunk state hpc count hc
    refine ⟨chunk_prefix_registersFit q full start chunk state hfit needs hend count hc.le,
      chunkOffset chunk + count, by omega, hp, (runOps_halted _ _ _).trans ha,
      (chunkCode start chunk).getD count RawCandidatePairScanWord.paddingOp, ?_,
      chunk_prefix_accessFits q full start chunk state count hc⟩
    rw [hp, show start + (chunkOffset chunk + count) = (start + chunkOffset chunk) + count by omega,
      natFetch_body containing ((start + chunkOffset chunk) + count) (by omega), decode_encode]
    have hh := hs.2 count hc
    rw [List.getD_eq_getElem containing RawCandidatePairScanWord.paddingOp (by omega)] at hh
    exact congrArg some hh
  · rw [chunk_run_prefix q full containing start hbound hcode chunk state hpc ha _ le_rfl]
    exact chunk_prefix_registersFit q full start chunk state hfit needs hend _ le_rfl

omit hbound hcode in
private theorem input_prefix (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

/-- Real full-width Word execution on controllerInput with its actual
appended initialUsed bits. No equal-run, all-prefix-safe or source-ROM
oracle is a caller premise. Linear allocation subsumes the proved eight
scratch words; the complete125-op loop remains a separate obligation. -/
theorem chunk_word_prefix (initialUsed : Finset (Fin q)) (chunk : Chunk) (state : NatState)
    (hpc : state.pc = 5 * (start + chunkOffset chunk)) (ha : state.halted = false)
    (hfit : RegistersFit (indexWidth 32 full.length q) state) (needs : Needs q full chunk state)
    (hend : Fits (indexWidth 32 full.length q) (5 * (start + 125)))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (count : Nat) (hc : count ≤ chunkLength chunk) :
    let runtime := CompactControllerClaims.controllerInput q full initialUsed
    let actual := packingRun runtime containing count (state.toWord (indexWidth 32 full.length q))
    let natural := natRun (rawIncidenceROM q full) containing count state
    actual = natural.toWord (indexWidth 32 full.length q) ∧
      (count < chunkLength chunk → actual.halted = false ∧
        actual.pc.toNat + 4 < (packingCode containing).length ∧
        ∃ op, PackingOp.decode (fetch containing actual) = some op ∧
          packingAccessFits runtime (linearLimit full.length q) actual op) := by
  let runtime := CompactControllerClaims.controllerInput q full initialUsed
  let bits := indexWidth 32 full.length q
  have safe := chunk_safe q full containing start hbound hcode chunk state hpc ha hfit needs hend
  have runEq (k : Nat) (hk : k ≤ chunkLength chunk) :
      natRun runtime containing k state = natRun (rawIncidenceROM q full) containing k state := by
    apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed) 8
    intro clock hclock _active op hd
    obtain ⟨_registers, _offset, _hoffset, _pc, _active, actualOp, decoded, access⟩ := safe.1 clock (by omega)
    have heq : op = actualOp := Option.some.inj (hd.symm.trans decoded)
    subst op
    exact access
  have word : packingRun runtime containing count (state.toWord bits) =
      (natRun (rawIncidenceROM q full) containing count state).toWord bits := by
    have proof := natRun_toWord runtime containing state count hwords (by
      intro k hk
      rw [runEq k (by omega)]
      have point := safe.1 k (by omega)
      exact ⟨point.1, point.pcFits hend⟩)
    exact proof.trans (congrArg (NatState.toWord bits) (runEq count hc))
  refine ⟨word, ?_⟩
  intro hstrict
  have point := safe.1 count hstrict
  have pcFit := point.pcFits hend
  obtain ⟨registers, offset, hoff, pc, active, op, decoded, access⟩ := point
  rw [word]
  have pcWord : ((natRun (rawIncidenceROM q full) containing count state).toWord bits).pc.toNat =
      5 * (start + offset) := by
    change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt pcFit, pc]
  refine ⟨active, ?_, op, ?_, ?_⟩
  · rw [pcWord, packingCode_length]
    omega
  · change PackingOp.decode (physicalFetch bits (packingCode containing)
      ((natRun (rawIncidenceROM q full) containing count state).toWord bits).pc.toNat) = _
    rw [pcWord, physicalFetch_eq _ _ _ hwords]
    change PackingOp.decode (natFetch containing (5 * (start + offset))) = some op
    simpa only [pc] using decoded
  · apply physical_access_of_nat runtime (linearLimit full.length q) _ _ registers
    cases op with
    | base instruction =>
      have tailAccess := PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed) 8 _ instruction access
      cases instruction with
      | subtract target left right => trivial
      | base original =>
        cases original <;> simp only [AccessFits] at tailAccess ⊢
        all_goals first | exact tailAccess | exact tailAccess.trans_le (by
          unfold linearLimit PA06A19PrepareCompactWord008.linearLimit
          omega)
    | arithmetic operation target left right => trivial
    | jumpIfZero condition target => trivial

end Linked

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactRetention020


