module

public import Paid.PDCompute_SolverOriginalGrid_111
public import Paid.PDCompute_SolverNumericScale_162
public import Paid.PDCompute_SolverScalarBits_152

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits

/-- Fine original bounds are RESET from logical entry equality at every
row/column, not iterated from a coarser temporary bound. -/
theorem solverEntry_fieldBits (P : Parameters) (fee penalty : ℚ) (n k row column : ℕ) (inside : row≤n) :
    ratEncodingBits (solverEntry P fee penalty k row column).observation≤solverStatsBits P fee n ∧
    ratEncodingBits (solverEntry P fee penalty k row column).repairs≤solverStatsBits P fee n ∧
    ratEncodingBits (solverEntry P fee penalty k row column).failure≤solverStatsBits P fee n := by
  simpa only [solverEntry_in_full P fee penalty n k row column inside,solverStatsBits] using
    arbitraryTable_fieldBits P fee penalty n k row column inside

theorem repairedEntry_fieldBits (entry : MenuEntry) (S : ℕ)
    (observation : ratEncodingBits entry.observation≤S) (repairs : ratEncodingBits entry.repairs≤S) (failure : ratEncodingBits entry.failure≤S) :
    ratEncodingBits (repairEntry entry).observation≤2*(S+3) ∧
    ratEncodingBits (repairEntry entry).repairs≤2*(S+3) ∧
    ratEncodingBits (repairEntry entry).failure≤2*(S+3) := by
  have add:=ratEncodingBits_add_le (1:ℚ) entry.repairs
  have oneSize : ratEncodingBits (1:ℚ)=3 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  rw [oneSize] at add
  change ratEncodingBits entry.observation≤2*(S+3) ∧ ratEncodingBits (1+entry.repairs)≤2*(S+3) ∧ ratEncodingBits entry.failure≤2*(S+3)
  omega

theorem badBranch_fieldBits (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools S : ℕ)
    (bounds : ∀ column,ratEncodingBits (previous.getD column abandonEntry).observation≤S ∧
      ratEncodingBits (previous.getD column abandonEntry).repairs≤S ∧ ratEncodingBits (previous.getD column abandonEntry).failure≤S) :
    ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.observation≤2*(S+3) ∧
    ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.repairs≤2*(S+3) ∧
    ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.failure≤2*(S+3) := by
  have abandoned : ratEncodingBits abandonEntry.observation≤2*(S+3) ∧ ratEncodingBits abandonEntry.repairs≤2*(S+3) ∧
      ratEncodingBits abandonEntry.failure≤2*(S+3) := by
    norm_num [abandonEntry,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    omega
  cases tools with
  | zero => exact abandoned
  | succ tools =>
    have child:=bounds tools
    have repaired:=repairedEntry_fieldBits (previous.getD tools abandonEntry) S child.1 child.2.1 child.2.2
    dsimp only [Parameters.menuBadBranch]
    split
    · exact repaired
    · exact abandoned

theorem solverRow_bad_fieldBits (P : Parameters) (fee penalty : ℚ) (n k row tools : ℕ) (inside : row≤n) :
    let bad:=(P.menuBadBranch fee penalty (solverRow P fee penalty k row) tools).2
    let R:=2*(solverStatsBits P fee n+3)
    ratEncodingBits bad.observation≤R ∧ ratEncodingBits bad.repairs≤R ∧ ratEncodingBits bad.failure≤R :=
  badBranch_fieldBits P fee penalty (solverRow P fee penalty k row) tools (solverStatsBits P fee n)
    (fun column=>solverEntry_fieldBits P fee penalty n k row column inside)

/-- BOTH actual good/bad objectives have one common fixed-depth bound.
The penalty size is added once, independently of n and M. -/
theorem solverRow_objective_bits (P : Parameters) (fee penalty : ℚ) (n k row tools : ℕ) (inside : row≤n) :
    let G:=16*(2*(solverStatsBits P fee n+3)+maximumMenuBits P fee+ratEncodingBits penalty+1)
    ratEncodingBits (((solverRow P fee penalty k row).getD tools abandonEntry).objective fee penalty)≤G ∧
    ratEncodingBits ((P.menuBadBranch fee penalty (solverRow P fee penalty k row) tools).2.objective fee penalty)≤G := by
  let S:=solverStatsBits P fee n
  let R:=2*(S+3)
  have widen : S≤R := by dsimp only [R]; omega
  have feeBound : ratEncodingBits fee≤maximumMenuBits P fee := (maximumMenuBits_bound P fee).2 fee (by simp [menuScalars])
  have good:=solverEntry_fieldBits P fee penalty n k row tools inside
  have bad:=solverRow_bad_fieldBits P fee penalty n k row tools inside
  exact ⟨(solverObjective_intermediate_bits _ fee penalty R (maximumMenuBits P fee) (ratEncodingBits penalty)
      (good.1.trans widen) (good.2.1.trans widen) (good.2.2.trans widen) feeBound (le_refl _)).2.2.2,
    (solverObjective_intermediate_bits _ fee penalty R (maximumMenuBits P fee) (ratEncodingBits penalty)
      bad.1 bad.2.1 bad.2.2 feeBound (le_refl _)).2.2.2⟩

end PDCompute.Solver
