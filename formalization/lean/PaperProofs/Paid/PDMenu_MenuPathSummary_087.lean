module

public import PaperProofs.Paid.PDMenu_MenuAnalysisEndpoint_086
public import PaperProofs.Paid.MenuCompiler

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Paid

/-- Analysis data only. No legality, performance or native-refinement
assertion is a field. The real compiled Policy is unchanged. -/
structure MenuPathRecord where
  observation : ℝ≥0∞
  physicalRepairs : ℕ
  failure : Bool

def menuPathFinish : MenuPathRecord := ⟨0, 0, false⟩
def menuPathAbandon : MenuPathRecord := ⟨0, 0, true⟩
def menuPathNonreturn : MenuPathRecord := ⟨⊤, 0, true⟩

abbrev MenuAnalysisSeed (n : ℕ) := Fin n → Bool
abbrev MenuAnalysisWorld (P : Parameters) (n : ℕ) := Fin n → Bool × P.experiment.Tape

/-- Samplewise recursion for the fixed original endpoint script. It is an
analysis definition, never a replacement Native execution or D27 program.
Exact correspondence with real run records is a separate proof obligation.
Nonreturn preserves infinite review spending and global failure. -/
noncomputable def menuPathSummary (P : Parameters) (table : MenuTable) :
    (n k : ℕ) → MenuAnalysisSeed n → MenuAnalysisWorld P n → MenuPathRecord
  | 0, _, _, _ => menuPathFinish
  | n + 1, k, seed, world => by
    classical
    exact match (Parameters.menuEntryAt table (n + 1) k).action with
    | .finish | .abandon => menuPathAbandon
    | .test level bad =>
        let test := menuAnalysisTest P level
        let stopped := test.rule.stop (seed 0) (world 0).2
        if stopped = ⊤ then menuPathNonreturn else
          let charge := P.experiment.observationCharge stopped
          let continuation :=
            if test.rule.decision (seed 0) (world 0).2 = (world 0).1 then
              menuPathSummary P table n k (Fin.tail seed) (Fin.tail world)
            else match bad with
              | .abandon => menuPathAbandon
              | .repair =>
                  if k = 0 then menuPathAbandon else
                    let child := menuPathSummary P table n (k - 1) (Fin.tail seed) (Fin.tail world)
                    { child with physicalRepairs := child.physicalRepairs + 1 }
          { continuation with observation := charge + continuation.observation }

theorem menuPathSummary_zero (P : Parameters) (table : MenuTable) (k : ℕ)
    (seed : MenuAnalysisSeed 0) (world : MenuAnalysisWorld P 0) :
    menuPathSummary P table 0 k seed world = menuPathFinish := rfl

theorem menuPathSummary_abandon (P : Parameters) (table : MenuTable) (n k : ℕ)
    (seed : MenuAnalysisSeed (n + 1)) (world : MenuAnalysisWorld P (n + 1))
    (ha : (Parameters.menuEntryAt table (n + 1) k).action = .abandon) :
    menuPathSummary P table (n + 1) k seed world = menuPathAbandon := by
  simp only [menuPathSummary, ha]

theorem menuPathSummary_finish_positive (P : Parameters) (table : MenuTable) (n k : ℕ)
    (seed : MenuAnalysisSeed (n + 1)) (world : MenuAnalysisWorld P (n + 1))
    (ha : (Parameters.menuEntryAt table (n + 1) k).action = .finish) :
    menuPathSummary P table (n + 1) k seed world = menuPathAbandon := by
  simp only [menuPathSummary, ha]

end PDMenu
