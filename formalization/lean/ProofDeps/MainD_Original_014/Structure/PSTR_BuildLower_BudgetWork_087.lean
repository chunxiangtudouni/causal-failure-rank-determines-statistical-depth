module

public import Structure.PSTR_BuildLower_ASTBudget_081

/-! The explicit compiler budget has the ORIGINAL work scale. The existing
source total-cost theorem is used only to bound source instruction count;
its virtual ROM and emitted code are not asserted to be supplied/executed by
the actual physical machine. A real whole-AST trace is still required. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ASTBudget
open IndexedRAM IndexedClosureRAM AlgorithmClaims PreparedLayout PA17ProgramTemplates041

theorem original_length_work (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) :
    (PA17TableBuild005.buildProgram full.length q (t q full)).length + 1 ≤ 32768 * work full.length q (t q full) := by
  have source := PA17Implementation030.prepared_build_totalCost q full hq hlaminar
  change totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q (t q full))
    (PA17QueryLayout014.heapWords full.length q (t q full)) ≤ 32768 * work full.length q (t q full) at source
  have counted : (PA17TableBuild005.buildProgram full.length q (t q full)).length + 1 ≤
      totalBuildCost (givenTreeROM q full) (PA17TableBuild005.buildProgram full.length q (t q full))
        (PA17QueryLayout014.heapWords full.length q (t q full)) := by
    rw [totalBuildCost, haltingWords_length]
    omega
  exact counted.trans source

theorem fullBuild_budget_work (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (environment : Nat → Nat) :
    budget fullBuild (dimensionROM full.length q (t q full)) ≤
      (factor fullBuild * 32768) * work full.length q (t q full) := by
  have counted := fullBuild_budget_original full.length q (t q full) environment
  have bound := Nat.mul_le_mul_left (factor fullBuild) (original_length_work q full hq hlaminar)
  exact counted.trans (by simpa only [Nat.mul_assoc] using bound)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ASTBudget
