module
public import Paid.PDCompute_Nat_ControlBudget_005
public import Paid.PDCompute_SolverNumericScale_162

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

/-- One fixed GLOBAL budget, allowed to retain larger rational scratch.
No phase must lower its current SafeBits to a smaller natural allowance. -/
structure ControlContext (caller : State) (incoming base n k origin span budget : ℕ) : Prop where
  initial : RootD27.Bits.SafeBits caller incoming
  fresh : caller.register .fresh=.natural base
  dominates : controlAllowance incoming n k origin span≤budget

theorem ControlContext.natural {caller : State} {incoming base n k origin span budget : ℕ}
    (context : ControlContext caller incoming base n k origin span budget) (value : ℕ)
    (bounded : value≤PDCompute.Pack.naturalCap base n k) : (.natural value : Cell).bits≤budget:=
  (controlAllowance_natural caller base incoming n k origin span value context.initial context.fresh bounded).trans context.dominates

theorem ControlContext.pc {caller : State} {incoming base n k origin span budget : ℕ}
    (context : ControlContext caller incoming base n k origin span budget) (counter : ℕ) (bounded : counter≤origin+span) :
    natBits counter≤budget:=(controlAllowance_pc incoming n k origin span counter bounded).trans context.dominates

theorem ControlContext.header {caller : State} {incoming base n k origin span budget : ℕ}
    (context : ControlContext caller incoming base n k origin span budget) : 1+natBits (base+headerWords)≤budget:=
  context.natural _ (baseHeader_le_cap base n k)

theorem ControlContext.small {caller : State} {incoming base n k origin span budget : ℕ}
    (context : ControlContext caller incoming base n k origin span budget) (value : ℕ) (bounded : value≤48) :
    (.natural value : Cell).bits≤budget:=context.natural _ (bounded.trans (PDCompute.Pack.naturalCap_small base n k))

theorem ControlContext.initial_safe {caller : State} {incoming base n k origin span budget : ℕ}
    (context : ControlContext caller incoming base n k origin span budget) : RootD27.Bits.SafeBits caller budget:=
  PDCompute.Pack.safeBits_mono context.initial (by have b:=context.dominates;unfold controlAllowance at b;omega)

abbrev SolverControlContext (caller : State) (incoming base n k : ℕ) (mode : ReaderMode) (origin budget : ℕ) :=
  ControlContext caller incoming base n k origin (solverCalleeCode mode origin).length budget

/-- Actual code fetch in the complete located program bounds an absolute
branch label. Neither a numeric-PC assumption nor a trace oracle appears. -/
theorem fetchedInstruction_le (origin : ℕ) (whole : Program) (counter : ℕ) (instruction : Instruction)
    (fetch : (locatedBlock origin whole)[counter]?=some instruction) : counter≤origin+whole.size := by
  obtain ⟨inside,_⟩:=Array.getElem?_eq_some_iff.mp fetch
  simp only [locatedBlock,Array.size_append,Array.size_replicate] at inside
  omega

theorem SolverControlContext.instruction {caller : State} {incoming base n k : ℕ} {mode : ReaderMode} {origin budget counter : ℕ}
    (context : SolverControlContext caller incoming base n k mode origin budget) (instruction : Instruction)
    (fetch : (solverLocatedProgram mode origin)[counter]?=some instruction) : natBits counter≤budget:=by
  have bound:=fetchedInstruction_le origin (solverCalleeCode mode origin).toArray counter instruction fetch
  exact context.pc counter (by simpa only [List.size_toArray] using bound)

theorem SolverControlContext.block {caller before : State} {incoming base n k : ℕ} {mode : ReaderMode} {origin budget : ℕ}
    (context : SolverControlContext caller incoming base n k mode origin budget) (block : List Instruction) (nonempty : 0<block.length)
    (fetch : FetchesCode (solverLocatedProgram mode origin) before.pc block) : natBits (before.pc+block.length)≤budget:=by
  have bound:=fetchedBlock_end_le origin (solverCalleeCode mode origin).toArray before.pc block nonempty fetch
  exact context.pc _ (by simpa only [List.size_toArray] using bound)

/-- Original162 scale plus ADDITIVE arbitrary caller carry, paid once.
This is a numerical bridge to the actual solver guard envelope, not an
assumption bounding dirty scratch by parameters alone. -/
def originalControlBudget (incoming : ℕ) (P : Parameters) (fee penalty : ℚ) (n k origin span : ℕ) : ℕ:=
  incoming+4194304*solverBitScale P fee penalty n k+natBits origin+natBits span+64

theorem controlContext_originalScale (caller : State) (incoming base n k origin span : ℕ) (P : Parameters) (fee penalty : ℚ)
    (safe : RootD27.Bits.SafeBits caller incoming) (fresh : caller.register .fresh=.natural base) :
    ControlContext caller incoming base n k origin span (originalControlBudget incoming P fee penalty n k origin span) := by
  refine ⟨safe,fresh,?_⟩
  have nk : natBits n+natBits k+1≤solverBitScale P fee penalty n k:=by unfold solverBitScale;omega
  unfold controlAllowance originalControlBudget
  omega

end PDCompute.NatControl
