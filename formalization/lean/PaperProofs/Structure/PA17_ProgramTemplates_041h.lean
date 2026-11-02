module
public import PaperProofs.Structure.PA17_ProgramTemplates_041e
public import PaperProofs.Structure.PA17_PackedTranslator_034a

/-! Exact fixed source template of the logical seven-word spill wrapper.
The appended index words are really cleared by generated ordinary code. -/
@[expose] public section
set_option maxRecDepth 20000
namespace PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17UniformGenerator035d
local instance pa17OfNat041h (n : Nat) : OfNat Expr n := ⟨.constant n⟩
local instance pa17Add041h : HAdd Expr Expr Expr := ⟨.binary .add⟩
local instance pa17Sub041h : HSub Expr Expr Expr := ⟨.binary .subtract⟩

def wipe (spillBase : Expr) : Program :=
  Program.sequence [.code [.constant .flag 0],
    .repeat 21 7 (.code [.constant .total (spillBase + (7 - .cell 21)), .storeHeap .total .flag]),
    .code [.constant .total 0]]

theorem wipe_eval (spillBase : Expr) (hf : 21 ∉ spillBase.cells) (rom : PhysicalROM) (environment : Nat → Nat) :
    (wipe spillBase).eval rom environment = PA17PackedTranslator034.wipe (spillBase.eval rom environment) := by
  have hloop : (Program.repeat 21 7 (.code [.constant .total (spillBase + (7 - .cell 21)),
      .storeHeap .total .flag])).eval rom environment = (List.range 7).flatMap
      (fun index => PA17PackedTranslator034.wipeBlock (spillBase.eval rom environment + index)) := by
    apply repeat_eval_ascending 21 7 _ _ _ 7 rfl
    intro index hi
    change [Op.base (.constant .total (spillBase.eval rom (Function.update environment 21 (7 - index)) +
      (7 - (7 - index)))), Op.base (.storeHeap .total .flag)] = _
    rw [eval_update_of_not_mem spillBase rom environment 21 _ hf, Nat.sub_sub_self hi.le]
    rfl
  simp only [wipe, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hloop]
  rfl

theorem wipe_uniformLength (spillBase : Expr) : (wipe spillBase).UniformLength := by
  dsimp [wipe, Program.UniformLength, Program.lengthExpr, Program.sequence, Expr.cells]
  decide

def logicalProgram (spillBase : Expr) (body : Program) : Program :=
  Program.sequence [wipe spillBase, body, wipe spillBase]

theorem logicalProgram_eval (spillBase : Expr) (body : Program) (hf : 21 ∉ spillBase.cells)
    (rom : PhysicalROM) (environment : Nat → Nat) :
    (logicalProgram spillBase body).eval rom environment =
      PA17PackedTranslator034.logicalProgram (spillBase.eval rom environment) (body.eval rom environment) := by
  simp only [logicalProgram, Program.sequence_eval, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    wipe_eval spillBase hf rom environment]
  rfl

theorem logicalProgram_uniformLength (spillBase : Expr) (body : Program) (hb : body.UniformLength) :
    (logicalProgram spillBase body).UniformLength := by
  exact ⟨wipe_uniformLength spillBase, hb, wipe_uniformLength spillBase, True.intro⟩

end PaperProofs.Structure.LaminarTree.PA17ProgramTemplates041
