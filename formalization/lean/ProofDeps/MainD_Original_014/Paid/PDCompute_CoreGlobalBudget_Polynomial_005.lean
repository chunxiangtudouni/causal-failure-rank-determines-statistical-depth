module
public import Paid.PDCompute_CoreGlobalBudget_Search_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000
@[expose] public section
namespace PDCompute.CoreGlobalBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits PDCompute.Solver PDCompute.CoreSearchBudget

theorem original_leading_le_scalarScale (P : Parameters) (fee : ℚ) :
    (P.certificate.stages+1)*(2*(P.certificate.M+1)+2)*(maximumMenuBits P fee+1)≤
      originalScalarScale P fee := by
  have menu : 1≤maximumMenuBits P fee := (maximumMenuBits_bound P fee).1
  have mul:=Nat.mul_le_mul_left ((P.certificate.stages+1)*(2*(P.certificate.M+1)+2)) menu
  simp only [Nat.mul_one] at mul
  have stats : (P.certificate.stages+1)*(2*(P.certificate.M+1)+2)*(maximumMenuBits P fee+1)≤
      solverStatsBits P fee P.certificate.stages := by
    unfold solverStatsBits
    nlinarith
  have scalar : solverStatsBits P fee P.certificate.stages≤originalScalarScale P fee := by
    unfold originalScalarScale uniformScalarScale
    omega
  exact stats.trans scalar

attribute [local irreducible] PolynomialBound

theorem coreOperandBound_original_polynomial : PolynomialBound PDROC.D27Prepare.Resources.size
    (fun x=>coreOperandBound x.1 x.2) := by
  have hs:=PDROC.D27Prepare.Resources.size_pos
  have base:=PolynomialBound.size PDROC.D27Prepare.Resources.size
  have data:=PDROC.D27Prepare.Resources.dataWeight_polynomial
  let c (n : ℕ):=PolynomialBound.constant PDROC.D27Prepare.Resources.size n
  have hQ : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.Q) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight PDROC.D27Prepare.Resources.countWeight;omega)
  have hM : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.M) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight PDROC.D27Prepare.Resources.countWeight;omega)
  have hGamma : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.1.certificate.gamma) :=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize;omega)
  have hRisk : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.1.certificate.risk) :=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have hRaw : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>rawSize x.1 x.2) :=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize;omega)
  have hJ : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.bisectionBudget x.2) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight numericalSize;omega)
  have hLambda : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.1.Lambda) :=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight;omega)
  have hScalar:=PDROC.D27Prepare.Resources.polynomial_of_fullInputSize original_scalarScale_polynomial
  have calibration:=(hQ.add (c 1) hs).mul (hGamma.add (c 2) hs)
  have search:=(hJ.add (c 1) hs).mul ((hLambda.add hRisk hs).add (c 1) hs)
  have bitsM:=PolynomialBound.natBits hs hM
  have bitsQ:=PolynomialBound.natBits hs hQ
  apply (((((hScalar.add calibration hs).add search hs).add hRaw hs).add bitsM hs).add bitsQ hs).add (c 1) hs |>.mono
  intro x
  have leading:=original_leading_le_scalarScale x.1 x.2
  unfold coreOperandBound
  omega

theorem coreOperandBound_full_polynomial : PolynomialBound fullInputSize (fun x=>coreOperandBound x.1 x.2) :=
  polynomial_full_of_original coreOperandBound_original_polynomial

theorem budget_full_polynomial (pcUpper : ℕ) :
    PolynomialBound fullInputSize (fun x=>budget x.1 x.2 pcUpper) :=
  ((PolynomialBound.constant fullInputSize (134217728+2*natBits pcUpper+256)).mul
    coreOperandBound_full_polynomial).mono (fun x=>budget_le_core x.1 x.2 pcUpper)

theorem budget_original_polynomial (pcUpper : ℕ) :
    PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>budget x.1 x.2 pcUpper) :=
  PDROC.D27Prepare.Resources.polynomial_of_fullInputSize (budget_full_polynomial pcUpper)

/-- Exactly the original variable-gamma input expression; constants and
degree precede ALL original P and fee. This proof needs no new fee sign. -/
theorem budget_original_uniform (pcUpper : ℕ) :
    ∃ C degree : ℕ,0<C ∧ ∀ (P : Parameters) (fee : ℚ),
      budget P fee pcUpper≤C*(variableGammaSize P fee)^degree := by
  have polynomial:=budget_original_polynomial pcUpper
  unfold PolynomialBound at polynomial
  obtain ⟨C,degree,positive,bound⟩:=polynomial
  exact ⟨C,degree,positive,fun P fee=>bound (P,fee)⟩

end PDCompute.CoreGlobalBudget
