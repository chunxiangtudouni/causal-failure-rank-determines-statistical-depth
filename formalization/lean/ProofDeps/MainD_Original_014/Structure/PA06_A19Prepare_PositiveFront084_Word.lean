module

public import Structure.PA06_A19Prepare_PositiveFront084
public import PaperProofs.Structure.PA17_UniformGenerator_035p
public import Structure.PA06_A19Prepare_InitialUsed037_Prefix

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED physical refinement of the SAME real positive-q17-step
gate prefix. Code-word/PC/B fit remain explicit internal static premises;
no original input supplies a future state, safety trace or output answer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveFront084

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceLaminarRAM PA17UniformGenerator035m

theorem word_prefix (rom : PhysicalROM) (N q handlerPC B H bits : Nat) (rest : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q) (small : 640 ≤ B) (boundN : N ≤ B) (boundQ : q ≤ B)
    (handler : handlerPC ≤ B) (input : 2 ≤ rom.input.length) (heap : 3 ≤ H)
    (bfit : Fits bits B) (words : WordsFit bits (packingCode (code handlerPC rest)))
    (pcfit : Fits bits (5 * (code handlerPC rest).length)) :
    (∀ count ≤ 17,
      packingRun rom (code handlerPC rest) count (natInitial.toWord bits) =
        (natRun rom (code handlerPC rest) count natInitial).toWord bits) ∧
      ∀ count < 17, PA06A19PrepareInitialUsed037.Fetched H rom (code handlerPC rest)
        (packingRun rom (code handlerPC rest) count (natInitial.toWord bits)) := by
  have safe := run_safe rom N q handlerPC B H rest headerN headerQ hq small boundN boundQ handler input heap
  constructor
  · intro count bound
    exact PA17UniformGenerator035p.actual_word_run rom B H bits (code handlerPC rest) 17 natInitial
      safe bfit words pcfit count bound
  · intro count bound
    exact PA17UniformGenerator035p.actual_word_fetch_access rom B H bits (code handlerPC rest) 17 natInitial
      safe bfit words pcfit count bound

/-- The comparison with the old checker is made ONLY at the common17-step
native endpoint. No continuation in the different old code is inferred. -/
theorem word_seventeen_eq (rom : PhysicalROM) (N q handlerPC B H bits : Nat) (rest : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q) (small : 640 ≤ B) (boundN : N ≤ B) (boundQ : q ≤ B)
    (handler : handlerPC ≤ B) (input : 2 ≤ rom.input.length) (heap : 3 ≤ H)
    (bfit : Fits bits B) (words : WordsFit bits (packingCode (code handlerPC rest)))
    (pcfit : Fits bits (5 * (code handlerPC rest).length)) :
    packingRun rom (code handlerPC rest) 17 (natInitial.toWord bits) =
      (natRun rom (checker ++ rest) 17 natInitial).toWord bits := by
  have hprefix := word_prefix rom N q handlerPC B H bits rest headerN headerQ hq small boundN boundQ
    handler input heap bfit words pcfit
  rw [hprefix.1 17 le_rfl]
  exact congrArg (NatState.toWord bits)
    (PA06A19PrepareEarlyGate079.positive_seventeen_eq rom q handlerPC rest headerQ hq)

private theorem word_control_of_refinement {bits : Nat}
    (native : NatState) (actual : WordState bits) (programLength endpointPC : Nat)
    (refinement : actual = native.toWord bits)
    (bounded : ∃ index ≤ programLength, native.pc = 5 * index)
    (pcfit : Fits bits (5 * programLength))
    (control : native.pc = endpointPC ∧ native.halted = false) :
    actual.pc.toNat = endpointPC ∧ actual.halted = false := by
  obtain ⟨index, bound, pc⟩ := bounded
  have endpointFit : Fits bits native.pc := by
    rw [pc]
    exact (Nat.mul_le_mul_left 5 bound).trans_lt pcfit
  have pcEq := congrArg (fun state : WordState bits => state.pc.toNat) refinement
  change actual.pc.toNat = (BitVec.ofNat bits native.pc).toNat at pcEq
  have nativeWordPC : (BitVec.ofNat bits native.pc).toNat = endpointPC := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt endpointFit, control.1]
  have activeEq := congrArg (fun state : WordState bits => state.halted) refinement
  change actual.halted = native.halted at activeEq
  exact ⟨pcEq.trans nativeWordPC, activeEq.trans control.2⟩

theorem word_seventeen_control (rom : PhysicalROM) (N q handlerPC B H bits : Nat) (rest : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q) (small : 640 ≤ B) (boundN : N ≤ B) (boundQ : q ≤ B)
    (handler : handlerPC ≤ B) (input : 2 ≤ rom.input.length) (heap : 3 ≤ H)
    (bfit : Fits bits B) (words : WordsFit bits (packingCode (code handlerPC rest)))
    (pcfit : Fits bits (5 * (code handlerPC rest).length)) :
    let after := packingRun rom (code handlerPC rest) 17 (natInitial.toWord bits)
    after.pc.toNat = (if N = 0 then 630 else 85) ∧ after.halted = false := by
  have safe := run_safe rom N q handlerPC B H rest headerN headerQ hq small boundN boundQ handler input heap
  have refined := PA17UniformGenerator035p.actual_word_run rom B H bits (code handlerPC rest) 17 natInitial
    safe bfit words pcfit 17 le_rfl
  have final := RunSafe.final B H rom (code handlerPC rest) 17 natInitial safe
  dsimp only
  exact word_control_of_refinement
    (natRun rom (code handlerPC rest) 17 natInitial)
    (packingRun rom (code handlerPC rest) 17 (natInitial.toWord bits))
    (code handlerPC rest).length (if N = 0 then 630 else 85)
    refined final.2.2 pcfit
    (PA06A19PrepareEarlyGate079.positive_seventeen_control rom N q handlerPC rest headerN headerQ hq)

end PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveFront084
