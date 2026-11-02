module
public import Paid.PDCompute_Nat_RowPointerBounds_004
public import Paid.PDCompute_Pack_BitBudget_057
public import Paid.PDCompute_SolverLocated_147

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatControl
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDCompute.Pack RootD27.Bits
open PDMenu.ComputeFrame

/-- ONE caller allowance; no per-row/column amplification and no bound
on arbitrary old scratch other than its incoming full-state certificate. -/
def controlAllowance (incoming n k origin span : ℕ) : ℕ:=incoming+natBits n+natBits k+natBits origin+natBits span+32

noncomputable def controlBudget (caller : State) (n k origin span : ℕ) : ℕ:=controlAllowance (initialBits caller) n k origin span

theorem controlAllowance_initial (caller : State) (incoming n k origin span : ℕ) (safe : SafeBits caller incoming) :
    SafeBits caller (controlAllowance incoming n k origin span):=safeBits_mono safe (by unfold controlAllowance;omega)

theorem controlAllowance_natural (caller : State) (base incoming n k origin span value : ℕ)
    (safe : SafeBits caller incoming) (fresh : caller.register .fresh=.natural base) (bounded : value≤naturalCap base n k) :
    (.natural value : Cell).bits≤controlAllowance incoming n k origin span := by
  have baseBits:=safe.register .fresh
  rw [fresh] at baseBits
  change 1+natBits base≤ incoming at baseBits
  have capBits:=naturalCap_bits base n k value bounded
  change 1+natBits value≤ incoming+natBits n+natBits k+natBits origin+natBits span+32
  omega

theorem controlAllowance_pc (incoming n k origin span counter : ℕ) (bounded : counter≤origin+span) :
    natBits counter≤controlAllowance incoming n k origin span := by
  have bound:=(natBits_mono bounded).trans (natBits_add_le origin span)
  unfold controlAllowance
  omega

/-- A literal fetched nonempty block in the COMPLETE located program
pays its real final linear counter. This derives scope from actual code
fetches, never a same-run or caller-supplied whole-trace PC oracle. -/
theorem fetchedBlock_end_le (origin : ℕ) (whole : Program) (counter : ℕ) (block : List Instruction)
    (nonempty : 0<block.length) (fetch : FetchesCode (PDMenu.ComputeFrame.locatedBlock origin whole) counter block) :
    counter+block.length≤origin+whole.size := by
  have inside : block.length-1<block.length:=by omega
  have literal : block[block.length-1]?=some block[block.length-1]:=List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩
  have fetched:= (fetch (block.length-1) inside).trans literal
  obtain ⟨indexBound,_⟩:=Array.getElem?_eq_some_iff.mp fetched
  simp only [PDMenu.ComputeFrame.locatedBlock,Array.size_append,Array.size_replicate] at indexBound
  omega

theorem controlBudget_initial (caller : State) (n k origin span : ℕ) : SafeBits caller (controlBudget caller n k origin span):=
  controlAllowance_initial caller _ n k origin span (initialBits_safe caller)

end PDCompute.NatControl
