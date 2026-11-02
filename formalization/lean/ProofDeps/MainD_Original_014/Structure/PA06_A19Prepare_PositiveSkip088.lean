module

public import Structure.PA06_A19Prepare_PositiveSkip088_Nat
public import Structure.PA06_A19Prepare_RuntimeHeader019
public import Structure.PA06_A19Prepare_InitialUsed037_Prefix
public import PaperProofs.Structure.PA17_UniformGenerator_035p

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED real positive tail skip in ONE fixed082 program.  Three
actual instructions reach its GLOBAL HALT PC while remaining active and
preserving the entire incoming heap.  Static eligibility is internal. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveSkip088

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims CompactControllerClaims
  PA17UniformGenerator035j PA17UniformGenerator035m PA17UniformGenerator035p
open PA06A19PrepareAllQCode082 (program bodyEnd finalEnd)

/-- Actual3-step skip, with no heap/register/data/safety/code qualification
beyond the preceding positive body's real PC and active endpoint.  The
jump itself is independent ofq, so this interface needs no additionalhq. -/
theorem actual_skip (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (before : WordState (indexWidth 32 full.length q))
    (pc : before.pc.toNat = 5 * bodyEnd) (active : before.halted = false) :
    let rom := controllerInput q full used
    let after := packingRun rom program 3 before
    after.pc.toNat = 5 * program.length ∧ after.halted = false ∧ after.heap = before.heap ∧
      (∀ count < 3, PA06A19PrepareInitialUsed037.Fetched
        (PA06A19PreparePreBuild044.allocation q full) rom program
        (packingRun rom program count before)) ∧
      (packingDynamicTrace rom program 3 before).length ≤ 36 := by
  let bits := indexWidth 32 full.length q
  let B := 2 ^ bits - 1
  let H := PA06A19PreparePreBuild044.allocation q full
  let rom := controllerInput q full used
  let native := PA06A19PrepareRuntimeHeader019.natView before
  have certificate := PA06A19PrepareAllQCode082.selected_certificate full.length q
  have targetFit : Fits bits (5 * finalEnd) := by
    rw [← PA06A19PrepareAllQCode082.program_length]
    exact certificate.2
  have targetBound : 5 * finalEnd ≤ B := by
    change 5 * finalEnd < 2 ^ bits at targetFit
    dsimp only [B]
    omega
  have safe := native_safe rom B H native pc active
    (PA06A19PrepareRuntimeHeader019.natView_registers before) targetBound
  have finish := native_finish rom native pc active
  have nativeWord : native.toWord bits = before :=
    PA06A19PrepareRuntimeHeader019.natView_toWord before
  have word (count : Nat) (bound : count ≤ 3) :
      packingRun rom program count before = (natRun rom program count native).toWord bits := by
    have actual := actual_word_run rom B H bits program 3 native safe
      (PA17GeneratorStatic048.maxWord_fits bits) certificate.1 certificate.2 count bound
    rw [nativeWord] at actual
    exact actual
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [word 3 le_rfl]
    change (BitVec.ofNat bits (natRun rom program 3 native).pc).toNat = 5 * program.length
    rw [finish.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt targetFit,
      PA06A19PrepareAllQCode082.program_length]
  · rw [word 3 le_rfl]
    exact finish.2.1
  · rw [word 3 le_rfl]
    funext address
    change BitVec.ofNat bits ((natRun rom program 3 native).heap address.toNat) = before.heap address
    rw [finish.2.2]
    simp only [native, PA06A19PrepareRuntimeHeader019.natView,
      BitVec.ofNat_toNat]
    simp only [bits, BitVec.setWidth_eq]
  · intro count bound
    have actual := actual_word_fetch_access rom B H bits program 3 native safe
      (PA17GeneratorStatic048.maxWord_fits bits) certificate.1 certificate.2 count bound
    rw [nativeWord] at actual
    exact actual
  · exact packingDynamicTrace_length_le rom program 3 before

end PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveSkip088
