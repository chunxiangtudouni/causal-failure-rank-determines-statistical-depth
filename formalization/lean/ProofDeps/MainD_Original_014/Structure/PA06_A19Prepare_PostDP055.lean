module

public import Structure.PA06_A19Prepare_PostDP055_Run
public import Structure.PA06_A19Prepare_PreBuildCards048

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED raw-controller to post-DP endpoint assembly.048 is called
once, then113 once on that actual endpoint and the SAME containing program.
This theorem deliberately has no whole-AST proper-prefix safety conclusion. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open CompactControllerClaims
open RawIncidenceLaminarRAM (natInitial)

def tail (right : List PackingOp) : List PackingOp :=
  PSTRBuildLower.CounterInit.builderCode 1639 ++ right

def program (right : List PackingOp) : List PackingOp :=
  PA06A19PreparePreBuild044.program (tail right)

def front (right : List PackingOp) : List PackingOp :=
  PA06A19PreparePreBuild044.clearFront (tail right) ++
    PA06A19PrepareClearVM045.programAt 1588

theorem front_length (right : List PackingOp) : (front right).length = 1639 := by
  simp only [front, List.length_append, PA06A19PreparePreBuild044.clearFront_length,
    PA06A19PrepareClearVM045.programAt_length]

theorem program_layout (right : List PackingOp) :
    front right ++ PSTRBuildLower.CounterInit.builderCode (front right).length ++ right =
      program right := by
  have layout := PA06A19PreparePreBuild044.clear_layout (tail right)
  rw [PA06A19PreparePreBuild044.clearFront_length] at layout
  rw [front_length]
  simpa only [front, program, tail, List.append_assoc] using layout

/-- Internal hcode/hpcfit are supplied by the final fixed-code certificate.
The original input provides no cache, no precomputed DP answer and no hSafe.
Its actual fullBuild output and the exact metadata/used entry come from one
combined clock. All original N=0 schedules remain admitted. -/
theorem raw_postDP_entry (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (right : List PackingOp)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (program right)))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * (program right).length)) :
    ∃ clock ≤ PA06A19PreparePreBuild044.clockBound q full + builderClockBound q full,
      let after := packingRun (controllerInput q full used) (program right) clock
        (natInitial.toWord (indexWidth 32 full.length q))
      Data q full after ∧
        after.pc = BitVec.ofNat _
          (5 * (1639 + (PSTRBuildLower.CounterInit.builderCode 1639).length)) ∧
        after.halted = false := by
  obtain ⟨preCount, preBound, prePost⟩ :=
    PA06A19PreparePreBuildCards048.raw_prebuild_cards_entry q full (tail right) used hq hl
      hpcfit hcode
  dsimp only at prePost
  rcases prePost with ⟨pre, _cards, raw, prePC, preActive, _rawPrefixSafe⟩
  let before := packingRun (controllerInput q full used) (program right) preCount
    (natInitial.toWord (indexWidth 32 full.length q))
  have pc : before.pc = BitVec.ofNat _ (5 * (front right).length) := by
    rw [front_length]
    have word : before.pc = BitVec.ofNat _ before.pc.toNat := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have nativePC : before.pc.toNat = 5 * 1639 := prePC
    rw [nativePC] at word
    exact word
  have code : WordsFit (indexWidth 32 full.length q)
      (packingCode (front right ++ PSTRBuildLower.CounterInit.builderCode (front right).length ++ right)) := by
    rw [program_layout]
    exact hcode
  have codePC : Fits (indexWidth 32 full.length q)
      (5 * (front right ++ PSTRBuildLower.CounterInit.builderCode (front right).length ++ right).length) := by
    rw [program_layout]
    exact hpcfit
  have built := builder_run q full used hq hl before pre raw (front right) right
    pc preActive code codePC
  rw [program_layout] at built
  obtain ⟨count, bound, post⟩ := built
  dsimp only at post
  refine ⟨preCount + count, Nat.add_le_add preBound bound, ?_⟩
  dsimp only
  rw [PA06A19PrepareRawHeader039Body.wordRun_add]
  refine ⟨post.1, ?_, post.2.2.1⟩
  simpa only [front_length] using post.2.1

end PaperProofs.Structure.LaminarTree.PA06A19PreparePostDP055
