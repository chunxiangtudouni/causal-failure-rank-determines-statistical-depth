module

public import Paid.PDCompute_SolverScanBody_047

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

def affineEndpointScore (P : Parameters) (good bad : ℚ) (index : ℕ) : ℚ :=
  let endpoint := P.cachedEndpoint P.endpointCache index
  endpoint.charge+(1-endpoint.error)*good+endpoint.error*bad

def cutoffPrefix (objective : ℕ → ℚ) (cutoff : ℚ) : ℕ → ℕ × ℚ
  | 0 => (0,cutoff)
  | index+1 =>
    let earlier := cutoffPrefix objective cutoff index
    if objective index < earlier.2 then (index,objective index) else earlier

theorem cutoffPrefix_succ (objective : ℕ → ℚ) (cutoff : ℚ) (last : ℕ) :
    cutoffPrefix objective cutoff (last+1)=cutoffScan objective cutoff last := by
  induction last with
  | zero => rfl
  | succ last ih => rw [cutoffPrefix,ih,cutoffScan]

structure ScanContents (P : Parameters) (values : ℕ → Cell) (source index : ℕ) (good bad cutoff : ℚ) : Prop where
  last : values 6=.natural P.certificate.M
  goodValue : values 21=.rational good
  badValue : values 22=.rational bad
  bestLevel : values 23=.natural (cutoffPrefix (affineEndpointScore P good bad) cutoff index).1
  bestValue : values 24=.rational (cutoffPrefix (affineEndpointScore P good bad) cutoff index).2
  counter : values 25=.natural index
  pointer : values 39=.natural (source+(1+2*index))

theorem scanAdvanceValues_preserves (values : ℕ → Cell) (index pointer slot : ℕ)
    (h25 : slot ≠ 25) (h39 : slot ≠ 39) :
    scanAdvanceValues values index pointer slot=values slot := by
  simp only [scanAdvanceValues,Function.update_of_ne h25,Function.update_of_ne h39]

theorem scanIterationValues_preserves (P : Parameters) (values : ℕ → Cell) (index source slot : ℕ)
    (good bad best : ℚ) (h23 : slot ≠ 23) (h24 : slot ≠ 24) (h25 : slot ≠ 25)
    (h26 : slot ≠ 26) (h27 : slot ≠ 27) (h28 : slot ≠ 28) (h29 : slot ≠ 29)
    (h30 : slot ≠ 30) (h39 : slot ≠ 39) :
    scanIterationValues P values index source good bad best slot=values slot := by
  unfold scanIterationValues
  rw [scanAdvanceValues_preserves _ _ _ _ h25 h39]
  split
  · exact (minimumUpdateValues_preserves _ slot h23 h24).trans
      (scanCandidateValues_preserves P values index good bad slot h26 h27 h28 h29 h30)
  · exact scanCandidateValues_preserves P values index good bad slot h26 h27 h28 h29 h30

theorem ScanContents.next {P : Parameters} {values : ℕ → Cell} {source index : ℕ} {good bad cutoff : ℚ}
    (contents : ScanContents P values source index good bad cutoff) :
    ScanContents P
      (scanIterationValues P values index source good bad
        (cutoffPrefix (affineEndpointScore P good bad) cutoff index).2)
      source (index+1) good bad cutoff := by
  let best := cutoffPrefix (affineEndpointScore P good bad) cutoff index
  let next := scanIterationValues P values index source good bad best.2
  have same (slot : ℕ) (h23 : slot ≠ 23) (h24 : slot ≠ 24) (h25 : slot ≠ 25)
      (h26 : slot ≠ 26) (h27 : slot ≠ 27) (h28 : slot ≠ 28) (h29 : slot ≠ 29)
      (h30 : slot ≠ 30) (h39 : slot ≠ 39) : next slot=values slot :=
    scanIterationValues_preserves P values index source slot good bad best.2 h23 h24 h25 h26 h27 h28 h29 h30 h39
  refine ⟨(same 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans contents.last,
    (same 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans contents.goodValue,
    (same 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans contents.badValue,
    ?_,?_,?_,?_⟩
  · rw [cutoffPrefix]
    change next 23=.natural (if affineEndpointScore P good bad index < best.2 then (index,affineEndpointScore P good bad index) else best).1
    dsimp only [next,scanIterationValues]
    rw [scanAdvanceValues_preserves _ _ _ 23 (by decide) (by decide)]
    change (if affineEndpointScore P good bad index < best.2 then
      minimumUpdateValues (scanCandidateValues P values index good bad) else scanCandidateValues P values index good bad) 23=
        .natural (if affineEndpointScore P good bad index < best.2 then (index,affineEndpointScore P good bad index) else best).1
    by_cases improved : affineEndpointScore P good bad index < best.2
    · simp only [ite_eq_left improved]
      simpa only [minimumUpdateValues,Function.update_of_ne (by decide : (23:ℕ) ≠ 24),Function.update_self]
        using (scanCandidateValues_preserves P values index good bad 25 (by decide) (by decide) (by decide) (by decide) (by decide)).trans contents.counter
    · simp only [ite_eq_right improved]
      exact (scanCandidateValues_preserves P values index good bad 23 (by decide) (by decide) (by decide) (by decide) (by decide)).trans contents.bestLevel
  · rw [cutoffPrefix]
    change next 24=.rational (if affineEndpointScore P good bad index < best.2 then (index,affineEndpointScore P good bad index) else best).2
    dsimp only [next,scanIterationValues]
    rw [scanAdvanceValues_preserves _ _ _ 24 (by decide) (by decide)]
    change (if affineEndpointScore P good bad index < best.2 then
      minimumUpdateValues (scanCandidateValues P values index good bad) else scanCandidateValues P values index good bad) 24=
        .rational (if affineEndpointScore P good bad index < best.2 then (index,affineEndpointScore P good bad index) else best).2
    by_cases improved : affineEndpointScore P good bad index < best.2
    · simp only [ite_eq_left improved]
      simpa only [minimumUpdateValues,Function.update_self,affineEndpointScore] using scanCandidateValues_objective P values index good bad
    · simp only [ite_eq_right improved]
      exact (scanCandidateValues_preserves P values index good bad 24 (by decide) (by decide) (by decide) (by decide) (by decide)).trans contents.bestValue
  · change next 25=.natural (index+1)
    rfl
  · change next 39=.natural (source+(1+2*(index+1)))
    simp only [next,scanIterationValues,scanAdvanceValues,Function.update_self]
    congr 1

end PDCompute.Solver
