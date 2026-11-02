module
public import PaperProofs.Structure.PA17_ProgramTemplates_041l
public import PaperProofs.Structure.PA17_QueryTemplates_044d
public import PaperProofs.Structure.PA17_WrappedNatRAM_038a

/-! Complete original rolling finish and both wrapped full/rolling programs.
The seven spill words are wiped by the same actual logical wrapper as038. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
local instance pa17OfNat041m (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041m : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Mul041m : HMul Expr Expr Expr := ⟨.binary .multiply⟩

def rollingCounts : Expr := rollingStageWord + 1
def rollingGoodFlags : Expr := rollingCounts + tDim
def rollingBadFlags : Expr := rollingGoodFlags + qDim + 2
def rollingRankWord : Expr := rollingBadFlags + qDim + 2

theorem rollingCounts_cells : rollingCounts.cells = ∅ := by simp [rollingCounts, Expr.cells, rollingStageWord_cells]
theorem rollingGoodFlags_cells : rollingGoodFlags.cells = ∅ := by simp [rollingGoodFlags, Expr.cells, rollingCounts_cells, tDim]
theorem rollingBadFlags_cells : rollingBadFlags.cells = ∅ := by simp [rollingBadFlags, Expr.cells, rollingGoodFlags_cells, qDim]

def rollingFinish : Program := Program.sequence [clearWord rollingStageWord,
  PA17QueryTemplates044a.countsProgram rollingCounts,
  PA17QueryTemplates044c.testsProgram rollingStageWord rollingCounts
    (rollingCapacity + tDim) (rollingCapacity + tDim) rollingGoodFlags rollingBadFlags,
  PA17QueryTemplates044d.rankProgram rollingGoodFlags rollingRankWord]

theorem rollingFinish_eval (N q size : Nat) (environment : Nat → Nat) :
    rollingFinish.eval (dimensionROM N q size) environment = PA17Rolling018B.finishProgram N q size := by
  have hp : (rollingCapacity + tDim).cells = ∅ := by simp [Expr.cells, rollingCapacity_cells, tDim]
  simp only [rollingFinish, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [clearWord_eval, PA17QueryTemplates044a.countsProgram_eval _ rollingCounts_cells,
    PA17QueryTemplates044c.testsProgram_eval _ _ _ _ _ _ rollingStageWord_cells rollingCounts_cells hp hp
      rollingGoodFlags_cells rollingBadFlags_cells,
    PA17QueryTemplates044d.rankProgram_eval _ _ rollingGoodFlags_cells]
  simp only [PA17Rolling018B.finishProgram, PA17Rolling018B.countProgram, PA17Rolling018B.testProgram,
    List.append_assoc]
  rfl

def rollingProgram : Program := .append rollingBuild rollingFinish

theorem rollingProgram_eval (N q size : Nat) (environment : Nat → Nat) :
    rollingProgram.eval (dimensionROM N q size) environment = PA17Rolling018B.program N q size := by
  rw [rollingProgram, Program.eval, rollingBuild_eval, rollingFinish_eval]
  rfl

def fullSpill : Expr := fullCapacity + 6 * tDim + nDim + 2 * qDim + 24
def rollingSpill : Expr := rollingCapacity + (4 * tDim + 2 * qDim + 7)
def wrappedFull : Program := logicalProgram fullSpill fullBuild
def wrappedRolling : Program := logicalProgram rollingSpill rollingProgram

theorem wrappedFull_eval (N q size : Nat) (environment : Nat → Nat) :
    wrappedFull.eval (dimensionROM N q size) environment = PA17WrappedNatRAM038a.implementation.buildProgram N q size := by
  rw [wrappedFull, logicalProgram_eval _ _ (by decide), fullBuild_eval]
  apply congrArg (fun spill => PA17PackedTranslator034.logicalProgram spill (PA17TableBuild005.buildProgram N q size))
  change (fullCapacity.eval (dimensionROM N q size) environment + 6 * size + N + 2 * q + 24) =
    PA17QueryLayout014.heapWords N q size
  rw [fullCapacity_eval]
  simp only [PA17QueryLayout014.heapWords, PA17QueryLayout014.indexWords, PA17QueryLayout014.capacityWords,
    PA17CellLayout003.capacityWords, PA17CellLayout003.workBase, Nat.add_assoc]

theorem wrappedRolling_eval (N q size : Nat) (environment : Nat → Nat) :
    wrappedRolling.eval (dimensionROM N q size) environment = PA17WrappedNatRAM038a.implementation.rollingProgram N q size := by
  rw [wrappedRolling, logicalProgram_eval _ _ (by decide), rollingProgram_eval]
  rfl

theorem rollingFinish_uniformLength : rollingFinish.UniformLength := by
  exact ⟨True.intro, PA17QueryTemplates044a.countsProgram_uniformLength _,
    PA17QueryTemplates044c.testsProgram_uniformLength _ _ _ _ _ _,
    PA17QueryTemplates044d.rankProgram_uniformLength _ _, True.intro⟩

theorem rollingProgram_uniformLength : rollingProgram.UniformLength :=
  ⟨rollingBuild_uniformLength, rollingFinish_uniformLength⟩

theorem wrappedFull_uniformLength : wrappedFull.UniformLength :=
  logicalProgram_uniformLength _ _ fullBuild_uniformLength

theorem wrappedRolling_uniformLength : wrappedRolling.UniformLength :=
  logicalProgram_uniformLength _ _ rollingProgram_uniformLength

theorem wrappedFull_codeTemplate (N q size : Nat) (environment : Nat → Nat) :
    wrappedFull.codeTemplate.denote (dimensionROM N q size) environment =
      (haltingWords (PA17WrappedNatRAM038a.implementation.buildProgram N q size)).length ::
        haltingWords (PA17WrappedNatRAM038a.implementation.buildProgram N q size) := by
  rw [Program.codeTemplate_denote _ _ _ wrappedFull_uniformLength, wrappedFull_eval]

theorem wrappedRolling_codeTemplate (N q size : Nat) (environment : Nat → Nat) :
    wrappedRolling.codeTemplate.denote (dimensionROM N q size) environment =
      (haltingWords (PA17WrappedNatRAM038a.implementation.rollingProgram N q size)).length ::
        haltingWords (PA17WrappedNatRAM038a.implementation.rollingProgram N q size) := by
  rw [Program.codeTemplate_denote _ _ _ wrappedRolling_uniformLength, wrappedRolling_eval]

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
