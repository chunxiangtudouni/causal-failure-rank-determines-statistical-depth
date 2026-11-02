module

public import Structure.PA06_A19Prepare_ZeroHeader080_Bounds
public import Structure.PA06_A19Prepare_InitialUsed037_Prefix

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual common32 zero-tool header from arbitrary incoming
Word heap/registers. Thus the genuine early gate's untouched heap needs no
extra field. The width is physically computed from the original ROM N/q;
no width, tree, t, metadata, table, hSafe or HeapRep answer is an input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  CompactControllerClaims PA17UniformGenerator035j PA17UniformGenerator035m PA17UniformGenerator035p

theorem represents_of_fields (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (state : WordState (wordBits full.length))
    (fields : NatHeader full.length (fun address => (state.heap (BitVec.ofNat _ address)).toNat)) :
    HeapRepresents 0 full 0 ⟨0, used, false⟩ state.heap := by
  rcases fields with ⟨h0, h1, h2, h3, h4, h5⟩
  have packed := zero_packed_words (wordBits full.length) (PA17PackingBounds043.bits_pos full.length 0)
  have one : (BitVec.ofNat (wordBits full.length) 1).toNat = 1 := by
    apply Nat.mod_eq_of_lt
    have hs := small_le_limit full.length
    unfold wordLimit at hs
    omega
  refine ⟨?_, h1, ?_, h3, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [treeSize, ↓reduceIte] using h0
  · rw [packed]
    exact h2
  · simpa only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords,
      BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] using h4
  · change (state.heap (BitVec.ofNat _ (4 + (BitVec.ofNat (wordBits full.length) 1).toNat))).toNat = 0
    rw [one]
    exact h5
  · intro position hp
    simp [staticMetadata] at hp
  · intro tool
    exact Fin.elim0 tool
  · intro hq
    omega

theorem actual_header (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (left right : List PackingOp) (before : WordState (wordBits full.length))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hcode : WordsFit (wordBits full.length) (packingCode (left ++ programAt left.length ++ right)))
    (hcodePC : Fits (wordBits full.length) (5 * (left ++ programAt left.length ++ right).length)) :
    let code := left ++ programAt left.length ++ right
    let rom := controllerInput 0 full used
    let after := packingRun rom code (clock full.length) before
    HeapRepresents 0 full 0 ⟨0, used, false⟩ after.heap ∧
      after.halted = false ∧ after.pc.toNat = 5 * (left.length + 60) ∧
      ∀ count < clock full.length, PA06A19PrepareInitialUsed037.Fetched (allocation full.length) rom code
        (packingRun rom code count before) := by
  let N := full.length
  let bits := wordBits N
  let B := wordLimit N
  let H := allocation N
  let rom := controllerInput 0 full used
  let code := left ++ programAt left.length ++ right
  let native := PA06A19PrepareRuntimeHeader019.natView before
  let after := packingRun rom code (clock N) before
  have Bfit : Fits bits B := limit_fits N
  have pcB : 5 * code.length ≤ B := by
    have hp : 5 * code.length < 2 ^ wordBits N := hcodePC
    dsimp only [B, wordLimit]
    omega
  have safe : RunSafe B H rom code (clock N) native :=
    program_safe full used B H left right native (small_le_limit N)
      (PA06A19PrepareRuntimeHeader019.heapWords_room N 0 0)
      (by simpa only [Nat.add_zero] using input_le_limit N) (bits_le_limit N) hpc ha
      (PA06A19PrepareRuntimeHeader019.natView_registers before) pcB
  have nativeWord : native.toWord bits = before := PA06A19PrepareRuntimeHeader019.natView_toWord before
  have word (count : Nat) (hc : count ≤ clock N) :
      packingRun rom code count before = (natRun rom code count native).toWord bits := by
    have actual := actual_word_run rom B H bits code (clock N) native safe Bfit hcode hcodePC count hc
    rw [nativeWord] at actual
    exact actual
  have sem := program_run full used left right native hpc ha
  dsimp only at sem
  have output (address value : Nat) (had : Fits bits address) (hval : Fits bits value)
      (written : (natRun rom code (clock N) native).heap address = value) :
      (after.heap (BitVec.ofNat bits address)).toNat = value := by
    have actual := actual_word_output rom B H bits code (clock N) native safe Bfit hcode hcodePC
      address value had hval written
    rw [nativeWord] at actual
    exact actual
  have small (value : Nat) (hv : value ≤ 69) : Fits bits value :=
    (hv.trans (small_le_limit N)).trans_lt Bfit
  have bitFit : Fits bits (indexWidth 32 full.length 0) := (bits_le_limit N).trans_lt Bfit
  rcases sem.2.2 with ⟨h0, h1, h2, h3, h4, h5⟩
  have fields : NatHeader N (fun address => (after.heap (BitVec.ofNat bits address)).toNat) :=
    ⟨output 0 0 (small 0 (by decide)) (small 0 (by decide)) h0,
     output 1 0 (small 1 (by decide)) (small 0 (by decide)) h1,
     output 2 0 (small 2 (by decide)) (small 0 (by decide)) h2,
     output 3 _ (small 3 (by decide)) bitFit h3,
     output 4 0 (small 4 (by decide)) (small 0 (by decide)) h4,
     output 5 0 (small 5 (by decide)) (small 0 (by decide)) h5⟩
  dsimp only
  refine ⟨represents_of_fields full used after fields, ?_, ?_, ?_⟩
  · rw [word _ le_rfl]
    exact sem.2.1
  · have exitFit : Fits bits (5 * (left.length + 60)) :=
      (show 5 * (left.length + 60) ≤ 5 * code.length by
        simp only [code, List.length_append, programAt_length]
        omega).trans_lt hcodePC
    rw [word _ le_rfl]
    change (BitVec.ofNat bits _).toNat = _
    rw [sem.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt exitFit]
  · intro count hc
    have actual := actual_word_fetch_access rom B H bits code (clock N) native safe Bfit hcode hcodePC count hc
    rw [nativeWord] at actual
    exact actual

end PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080
