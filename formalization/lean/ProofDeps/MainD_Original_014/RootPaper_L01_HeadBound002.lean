module

public import RootPaper_L01_Core001

/-! The original positive-N/positive-q paper bound, projected from the
already accepted actual heads run. Degenerate branches retain PreparedRun's
original exact headWork bound; no positivity premise is added to them. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.L01

open PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Structure PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

theorem headWork_le_Nqt {q : Nat} (full : List (Finset (Fin q)))
    (stages : 0 < full.length) (tools : 0 < q) :
    CompactPrice.headWork q full ≤ 4 * (full.length * q * treeSize q full) := by
  have stageBound : full.length + 1 ≤ 2 * full.length := by omega
  have toolBound : q + 1 ≤ 2 * q := by omega
  unfold CompactPrice.headWork liveWork
  rw [ite_eq_right (Nat.ne_of_gt tools)]
  unfold queryWork
  calc
    (full.length + 1) * ((q + 1) * treeSize q full) =
        ((full.length + 1) * (q + 1)) * treeSize q full := by ring
    _ ≤ ((2 * full.length) * (2 * q)) * treeSize q full :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul stageBound toolBound)
    _ = 4 * (full.length * q * treeSize q full) := by ring

theorem prepared_heads_Nqt {q : Nat} (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (prepSteps headSteps : Nat)
    (prepared : RootPaper.Table.PreparedRun full used prepSteps headSteps)
    (stages : 0 < full.length) (tools : 0 < q) :
    callCost q full RootPaper.Table.heads .query headSteps
        (RootPaper.Table.preparedHeap full used prepSteps) ≤
      120000 * (full.length * q * treeSize q full) := by
  calc
    _ ≤ 30000 * CompactPrice.headWork q full := prepared.2.2.2.2.2.1
    _ ≤ 30000 * (4 * (full.length * q * treeSize q full)) :=
      Nat.mul_le_mul_left _ (headWork_le_Nqt full stages tools)
    _ = 120000 * (full.length * q * treeSize q full) := by ring

#print axioms RootPaper.L01.headWork_le_Nqt
#print axioms RootPaper.L01.prepared_heads_Nqt

end RootPaper.L01
