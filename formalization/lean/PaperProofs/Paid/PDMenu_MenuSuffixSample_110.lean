module

public import PaperProofs.Paid.PDMenu_MenuAnalysisLaw_088

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Crop hidden analysis data only. Native stages, tools, handles and
visible histories stay in the original physical N-stage machine. -/
def menuSuffixStage (N K cursor n : ℕ) (hfit : cursor + n = N) (i : Fin n) : (freshInstance N K).Stage :=
  ⟨cursor + i.val, by simpa [freshInstance] using (Nat.add_lt_add_left i.isLt cursor).trans_eq hfit⟩

def menuSuffixSeed (N K cursor n : ℕ) (hfit : cursor + n = N) (seed : MenuSeed N K) : MenuAnalysisSeed n :=
  fun i => seed (menuSuffixStage N K cursor n hfit i)

def menuSuffixWorld (P : Parameters) (N K cursor n : ℕ) (hfit : cursor + n = N)
    (fee : ℚ) (hfee : 0 ≤ fee) (world : (P.freshInput N K fee hfee).World) : MenuAnalysisWorld P n :=
  fun i => world (menuSuffixStage N K cursor n hfit i)

theorem menuSuffixStage_zero (N K cursor n : ℕ) (hfit : cursor + (n + 1) = N)
    (stage : (freshInstance N K).Stage) (hstage : stage.val = cursor) :
    menuSuffixStage N K cursor (n + 1) hfit 0 = stage := Fin.ext (by simp only [menuSuffixStage, Fin.val_zero, Nat.add_zero, hstage])

theorem menuSuffixStage_succ (N K cursor n : ℕ) (hfit : cursor + (n + 1) = N)
    (hnext : cursor + 1 + n = N) (i : Fin n) :
    menuSuffixStage N K cursor (n + 1) hfit i.succ = menuSuffixStage N K (cursor + 1) n hnext i :=
  Fin.ext (by dsimp only [menuSuffixStage, Fin.val_succ]; omega)

theorem menuSuffixSeed_tail (N K cursor n : ℕ) (hfit : cursor + (n + 1) = N)
    (hnext : cursor + 1 + n = N) (seed : MenuSeed N K) :
    Fin.tail (menuSuffixSeed N K cursor (n + 1) hfit seed) = menuSuffixSeed N K (cursor + 1) n hnext seed := by
  funext i
  exact congrArg seed (menuSuffixStage_succ N K cursor n hfit hnext i)

theorem menuSuffixWorld_tail (P : Parameters) (N K cursor n : ℕ) (hfit : cursor + (n + 1) = N)
    (hnext : cursor + 1 + n = N) (fee : ℚ) (hfee : 0 ≤ fee) (world : (P.freshInput N K fee hfee).World) :
    Fin.tail (menuSuffixWorld P N K cursor (n + 1) hfit fee hfee world) =
      menuSuffixWorld P N K (cursor + 1) n hnext fee hfee world := by
  funext i
  exact congrArg (α := (freshInstance N K).Stage) (β := Bool × P.experiment.Tape) (fun stage => world stage)
    (menuSuffixStage_succ N K cursor n hfit hnext i)

theorem menuSuffixSeed_root (N K : ℕ) (seed : MenuSeed N K) :
    menuSuffixSeed N K 0 N (Nat.zero_add N) seed = menuSeedFinEquiv N K seed := by
  funext i
  exact congrArg seed (Fin.ext (Nat.zero_add i.val))

theorem menuSuffixWorld_root (P : Parameters) (N K : ℕ) (fee : ℚ) (hfee : 0 ≤ fee)
    (world : (P.freshInput N K fee hfee).World) :
    menuSuffixWorld P N K 0 N (Nat.zero_add N) fee hfee world = menuWorldFinEquiv P N K fee hfee world := by
  funext i
  have hs : menuSuffixStage N K 0 N (Nat.zero_add N) i = menuStageAt N K i := Fin.ext (Nat.zero_add i.val)
  exact congrArg (α := (freshInstance N K).Stage) (β := Bool × P.experiment.Tape) (fun stage => world stage) hs

end PDMenu
