module

public import Structure.PA06_A19Prepare_HeaderScratch024_Runtime
public import Structure.PA06_A19Prepare_CompactWord008

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! The original104-op save/header/restore block at its actual absolute
PC in an arbitrary containing program. Incoming data bounds come from
the physical Word view. This is a genuine embedded execution theorem;
neither the incoming PC nor the heap is reset. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRawHeader039Body

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawTreePreprocessingClaims RawIncidenceScanSafety
  PA17UniformGenerator035a PA17UniformGenerator035m PA17UniformGenerator035p

abbrev headerProgram := PA06A19PrepareHeaderScratch024.program
abbrev headerClock := PA06A19PrepareHeaderScratch024.clock
abbrev heapWords := PA06A19PrepareRuntimeHeader019.heapWords

/-- Standard iteration law for the actual physical packingRun. The proof
uses its original recursion, exactly as the existing finite-init helper. -/
theorem wordRun_add {bits : Nat} (rom : PhysicalROM) (code : List PackingOp)
    (left right : Nat) (state : WordState bits) :
    packingRun rom code (left + right) state = packingRun rom code right (packingRun rom code left state) := by
  induction left generalizing state with
  | zero => simp only [Nat.zero_add, packingRun]
  | succ left ih =>
    rw [Nat.succ_add]
    change packingRun rom code (left + right) (packingStep rom ((packingCode code).map (BitVec.ofNat bits)) state) = _
    exact ih _

theorem packingAccess_mono {bits : Nat} (rom : PhysicalROM) (small large : Nat)
    (room : small ≤ large) (state : WordState bits) (op : PackingOp)
    (access : packingAccessFits rom small state op) : packingAccessFits rom large state op := by
  cases op with
  | base op =>
    cases op with
    | subtract target left right => trivial
    | base instruction =>
      cases instruction <;> simp only [packingAccessFits, AccessFits] at access ⊢
      all_goals first | exact access | exact access.trans_le room
  | arithmetic operation target left right => trivial
  | jumpIfZero condition target => trivial

theorem compact_room (N q t : Nat) (hq : 0 < q) :
    PA06A19PrepareCompactWord008.linearLimit N q ≤ heapWords N q t := by
  unfold PA06A19PrepareCompactWord008.linearLimit heapWords PA06A19PrepareRuntimeHeader019.heapWords
  omega

/-- Same104-op block, actual containing-code fetch and actual incoming
Word state. No safety, source-cache value or width16 premise is supplied. -/
theorem embedded_header (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (t : Nat) (hq : 0 < q)
    (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ headerProgram left.length ++ right).length))
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ headerProgram left.length ++ right))) :
    let code := left ++ headerProgram left.length ++ right
    let actual := packingRun (CompactControllerClaims.controllerInput q full used) code (headerClock full.length q) state
    actual.pc.toNat = 5 * (left.length + 104) ∧ actual.halted = false ∧
      PA06A19PrepareRuntimePacked016.Header q actual.heap ∧
      (∀ address : BitVec (indexWidth 32 full.length q), 16 ≤ address.toNat → actual.heap address = state.heap address) ∧
      ∀ count < headerClock full.length q,
        let current := packingRun (CompactControllerClaims.controllerInput q full used) code count state
        current.halted = false ∧ current.pc.toNat + 4 < (packingCode code).length ∧
          ∃ op, PackingOp.decode (fetch code current) = some op ∧
            packingAccessFits (CompactControllerClaims.controllerInput q full used) (heapWords full.length q t) current op := by
  let bits := indexWidth 32 full.length q
  let B := 2 ^ bits - 1
  let rom := CompactControllerClaims.controllerInput q full used
  let code := left ++ headerProgram left.length ++ right
  let start := PA06A19PrepareRuntimeHeader019.natView state
  let final := natRun rom code (headerClock full.length q) start
  have hb64 : 64 ≤ bits := PA17GeneratorStatic048.bits_ge_64 full.length q hq
  have startPC : start.pc = 5 * left.length := hpc
  have values (index : Nat) (hi : index < 5) : start.heap (64 + index) ≤ B := by
    have fits : (state.heap (BitVec.ofNat bits (64 + index))).toNat < 2 ^ bits :=
      (state.heap (BitVec.ofNat bits (64 + index))).isLt
    change (state.heap (BitVec.ofNat bits (64 + index))).toNat ≤ 2 ^ bits - 1
    omega
  have pcB : 5 * code.length ≤ B := by
    change 5 * code.length < 2 ^ bits at hend
    omega
  have safe := PA06A19PrepareHeaderScratch024.program_safe q full used t hq left right start startPC ha
    (PA06A19PrepareRuntimeHeader019.natView_registers state) values pcB
  have word (count : Nat) (hc : count ≤ headerClock full.length q) :
      packingRun rom code count state = (natRun rom code count start).toWord bits := by
    have actual := actual_word_run rom B (heapWords full.length q t) bits code (headerClock full.length q) start safe
      (PA17GeneratorStatic048.maxWord_fits bits) hcode hend count hc
    rw [PA06A19PrepareRuntimeHeader019.natView_toWord] at actual
    exact actual
  have native := PA06A19PrepareHeaderScratch024.program_run q full used left right start startPC ha
  have header : PA06A19PrepareHeaderScratch024.NatHeader q full.length final.heap := native.2.2.1
  have endFit : Fits bits (5 * (left.length + 104)) := by
    have length : code.length = left.length + 104 + right.length := by
      simp only [code, List.length_append, PA06A19PrepareHeaderScratch024.program_length]
    have codeFits : Fits bits (5 * code.length) := hend
    exact (by omega : 5 * (left.length + 104) ≤ 5 * code.length).trans_lt codeFits
  have h0 : (BitVec.ofNat bits 0).toNat = 0 := PA06A19PrepareHeaderScratch024.small_toNat (by omega) 0 (by decide)
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := PA06A19PrepareHeaderScratch024.small_toNat (by omega) 1 (by decide)
  have h2 : (BitVec.ofNat bits 2).toNat = 2 := PA06A19PrepareHeaderScratch024.small_toNat (by omega) 2 (by decide)
  have h3 : (BitVec.ofNat bits 3).toNat = 3 := PA06A19PrepareHeaderScratch024.small_toNat (by omega) 3 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [word _ le_rfl]
    change (BitVec.ofNat bits final.pc).toNat = _
    rw [native.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt endFit]
  · rw [word _ le_rfl]
    exact native.2.1
  · rw [word _ le_rfl]
    constructor
    · change BitVec.ofNat bits (final.heap (BitVec.ofNat bits 0).toNat) = _
      rw [h0, header.1]
    · change BitVec.ofNat bits (final.heap (BitVec.ofNat bits 1).toNat) = _
      rw [h1, header.2.1]
      rfl
    · change BitVec.ofNat bits (final.heap (BitVec.ofNat bits 2).toNat) = _
      rw [h2, header.2.2.1]
    · change BitVec.ofNat bits (final.heap (BitVec.ofNat bits 3).toNat) = _
      rw [h3, header.2.2.2]
  · intro address above
    rw [word _ le_rfl]
    change BitVec.ofNat bits (final.heap address.toNat) = state.heap address
    rw [native.2.2.2 address.toNat above]
    change BitVec.ofNat bits ((state.heap (BitVec.ofNat bits address.toNat)).toNat) = state.heap address
    simp only [bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro count hc
    have physical := actual_word_fetch_access rom B (heapWords full.length q t) bits code (headerClock full.length q)
      start safe (PA17GeneratorStatic048.maxWord_fits bits) hcode hend count hc
    rw [PA06A19PrepareRuntimeHeader019.natView_toWord] at physical
    exact physical

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRawHeader039Body
