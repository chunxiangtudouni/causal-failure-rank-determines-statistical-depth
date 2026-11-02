module

public import Paid.PDCompute_SolverInputBits_190
public import Paid.PDCompute_SolverStandaloneCode_148
public import Paid.PDCompute_SolverNumericScale_162
public import Paid.PDCompute_Nat_Resources_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame PDCompute.NatControl
open PDROC.CalibrationRow.Operand

attribute [local irreducible] fullCellCode cellFieldsCode matrixCode matrixPackCode solverCalleeCode solverOutputOrigin

def solverLoaderBudget (P : Parameters) (fee penalty : ℚ) (n k : ℕ) : ℕ :=
  solverBitScale P fee penalty n k+natBits solverOutputOrigin+32

noncomputable def solverStandaloneBudget (P : Parameters) (fee penalty : ℚ) (n k : ℕ) : ℕ :=
  originalControlBudget (PDCompute.Pack.initialBits (solverInputResult initial solverOutputOrigin n k fee penalty)) P fee penalty n k 11
    (solverCalleeCode .inputROM 11).length

/-- A CLOSED program constant, chosen before every original input. No
evaluation of the large fixed literal program is needed for uniformity. -/
def solverStandaloneBitConstant : ℕ :=
  4194405+natBits solverOutputOrigin+natBits (solverCalleeCode .inputROM 11).length

theorem solver_initial_safe : RootD27.Bits.SafeBits initial 2 := by
  apply RootD27.Bits.SafeBits.of_fields
  · intro register
    change (.natural 0 : Cell).bits≤2
    decide
  · intro address live
    change address∈(∅ : Finset ℕ) at live
    simp at live
  · intro address live
    change address∈(∅ : Finset ℕ) at live
    simp at live
  · intro value member
    change value∈([] : List Cell) at member
    cases member
  · change natBits 0≤2
    decide

theorem solver_loader_budget_guards (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    let budget:=solverLoaderBudget P fee penalty n k
    4≤budget ∧ (.natural n : Cell).bits≤budget ∧ (.natural k : Cell).bits≤budget ∧ (.rational fee : Cell).bits≤budget ∧
    (.rational penalty : Cell).bits≤budget ∧ (.natural solverOutputOrigin : Cell).bits≤budget ∧ natBits (initial.pc+11)≤budget := by
  have data:=solverBitScale_data P fee penalty n k
  have pen:=solverBitScale_penalty P fee penalty n k
  have feeBound : ratEncodingBits fee≤maximumMenuBits P fee := (maximumMenuBits_bound P fee).2 fee (by simp [menuScalars])
  have dimensions : natBits n+natBits k≤solverBitScale P fee penalty n k := by unfold solverBitScale;omega
  have pc : natBits (initial.pc+11)=4 := by decide
  simp only [solverLoaderBudget,Cell.bits,pc]
  omega

theorem solver_loaded_safe (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    RootD27.Bits.SafeBits (solverInputResult initial solverOutputOrigin n k fee penalty) (solverLoaderBudget P fee penalty n k) := by
  have guards:=solver_loader_budget_guards P fee penalty n k
  have initialSafe:=PDCompute.Pack.safeBits_mono solver_initial_safe (by have small:=guards.1;omega : 2≤solverLoaderBudget P fee penalty n k)
  have bounded:=solverInputCode_prefix_safe P fee penalty n k solverOutputOrigin (solverLoaderBudget P fee penalty n k) initial initialSafe guards.1
    guards.2.1 guards.2.2.1 guards.2.2.2.1 guards.2.2.2.2.1 guards.2.2.2.2.2.1 guards.2.2.2.2.2.2
  exact bounded.final (solverInputCode_execute P fee penalty n k solverOutputOrigin initial)

theorem initialBits_le_of_safe (state : State) (budget : ℕ) (safe : RootD27.Bits.SafeBits state budget) :
    PDCompute.Pack.initialBits state≤budget := by
  apply PDCompute.Pack.safeBits_peak
  intro current member
  have same:=List.mem_singleton.mp member
  subst current
  exact safe

theorem solver_loaded_initialBits_bound (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    PDCompute.Pack.initialBits (solverInputResult initial solverOutputOrigin n k fee penalty)≤solverLoaderBudget P fee penalty n k :=
  initialBits_le_of_safe _ _ (solver_loaded_safe P fee penalty n k)

theorem solver_standalone_budget_uniform (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    solverStandaloneBudget P fee penalty n k≤solverStandaloneBitConstant*solverBitScale P fee penalty n k := by
  have loaded:=solver_loaded_initialBits_bound P fee penalty n k
  have positive:=solverBitScale_positive P fee penalty n k
  have staticBound:=Nat.mul_le_mul_left (100+natBits solverOutputOrigin+natBits (solverCalleeCode .inputROM 11).length) positive
  simp only [Nat.mul_one] at staticBound
  have eleven : natBits 11=4 := by decide
  unfold solverStandaloneBudget originalControlBudget solverLoaderBudget solverStandaloneBitConstant at *
  rw [eleven]
  nlinarith

theorem solver_standalone_emit_pc (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    natBits solverHaltPC≤solverStandaloneBudget P fee penalty n k := by
  let loaded:=solverInputResult initial solverOutputOrigin n k fee penalty
  have carried:=(PDCompute.Pack.initialBits_safe loaded).register .old
  change 1+natBits solverOutputOrigin≤PDCompute.Pack.initialBits loaded at carried
  have fixed:=PDCompute.Pack.origin_pc_bits solverOutputOrigin solverHaltPC (by unfold solverHaltPC;omega)
  dsimp only [loaded] at carried
  unfold solverStandaloneBudget originalControlBudget
  omega

end PDCompute.Solver
