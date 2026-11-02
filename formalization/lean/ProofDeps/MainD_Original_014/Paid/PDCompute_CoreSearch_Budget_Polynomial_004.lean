module
public import Paid.PDCompute_CoreSearch_Budget_Search_003
public import Paid.PDROC_D27Prepare_Resources_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreSearchBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDLower.CoreSearch

theorem maximumMenuBits_le_menuEncodingSize (P : Parameters) (fee : ℚ) : maximumMenuBits P fee≤menuEncodingSize P fee:=by
  have bounded:=menuEncodingSize_bound P fee
  have fold (values : List ℕ) : ∀ starting,starting≤menuEncodingSize P fee→
      (∀ value∈values,value≤menuEncodingSize P fee)→values.foldl max starting≤menuEncodingSize P fee:=by
    induction values with
    | nil=>intro starting inside _;exact inside
    | cons value values ih=>
      intro starting inside all
      exact ih (max starting value) (max_le inside (all value (by simp)))
        (fun next member=>all next (List.mem_cons_of_mem value member))
  apply fold _ 1 bounded.1
  intro value member
  obtain ⟨scalar,inside,rfl⟩:=List.mem_map.mp member
  exact bounded.2 scalar inside

theorem original_size_le_full (x : DataInput) : PDROC.D27Prepare.Resources.size x≤3*fullInputSize x:=by
  have bits : natBits x.1.tools≤x.1.tools+1:=Nat.add_le_add_right (Nat.log2_le_self _) 1
  have tools:=x.1.tools_lt_stages.le
  unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize fullInputSize
  omega

theorem polynomial_full_of_original {value : DataInput→ℕ}
    (bounded : PolynomialBound PDROC.D27Prepare.Resources.size value) : PolynomialBound fullInputSize value:=by
  obtain ⟨C,degree,positive,bound⟩:=bounded
  refine ⟨C*3^degree,degree,Nat.mul_pos positive (pow_pos (by decide) _),?_⟩
  intro x
  calc
    value x≤C*(PDROC.D27Prepare.Resources.size x)^degree:=bound x
    _≤C*(3*fullInputSize x)^degree:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left (original_size_le_full x) degree)
    _=(C*3^degree)*(fullInputSize x)^degree:=by rw [mul_pow];ring

attribute [local irreducible] PolynomialBound

/-- Existing original data/count polynomial is used only to prove a
polynomial envelope. The actual scalarScale itself contains NO encoded
table size or tools/entry-count multiplier. -/
theorem original_scalarScale_polynomial : PolynomialBound fullInputSize (fun x=>originalScalarScale x.1 x.2):=by
  apply polynomial_full_of_original
  have hs:=PDROC.D27Prepare.Resources.size_pos
  have base:=PolynomialBound.size PDROC.D27Prepare.Resources.size
  have data:=PDROC.D27Prepare.Resources.dataWeight_polynomial
  let c (n : ℕ):=PolynomialBound.constant PDROC.D27Prepare.Resources.size n
  have hN : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.stages):=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have hM : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.M):=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight PDROC.D27Prepare.Resources.countWeight;omega)
  have hQ : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.certificate.Q):=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight PDROC.D27Prepare.Resources.countWeight;omega)
  have hGamma : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.1.certificate.gamma):=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have hReview : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.1.reviewFee):=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have hFee : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.2):=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have hRisk : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.1.certificate.risk):=
    base.mono (by intro x;unfold PDROC.D27Prepare.Resources.size variableGammaSize rawSize;omega)
  have hJ : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>x.1.bisectionBudget x.2):=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight numericalSize;omega)
  have hLambda : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>ratEncodingBits x.1.Lambda):=
    data.mono (by intro x;unfold PDROC.D27Prepare.Resources.dataWeight;omega)
  have hbM:=PolynomialBound.natBits hs hM
  have hbN:=PolynomialBound.natBits hs hN
  have menu : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>menuEncodingSize x.1 x.2):=by
    unfold menuEncodingSize
    exact ((c 512).mul (hQ.add (c 1) hs)).mul ((((hGamma.add hReview hs).add hFee hs).add hbM hs).add (c 2) hs)
  have maxMenu : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>maximumMenuBits x.1 x.2):=
    menu.mono (fun x=>maximumMenuBits_le_menuEncodingSize x.1 x.2)
  have stats : PolynomialBound PDROC.D27Prepare.Resources.size (fun x=>solverStatsBits x.1 x.2 x.1.certificate.stages):=by
    unfold solverStatsBits
    have rows:=hN.add (c 1) hs
    have endpoints:=((c 2).mul (hM.add (c 1) hs)).add (c 2) hs
    exact (((c 2).mul ((rows.mul endpoints).mul maxMenu)).add
      ((c 64).mul ((maxMenu.add hbN hs).add (c 1) hs)) hs).add (c 2) hs
  have price:=((c 8).mul ((hJ.add hLambda hs).add (c 2) hs))
  unfold originalScalarScale uniformScalarScale priceBudget
  exact (((price.add stats hs).add hRisk hs).add hFee hs).add (c 1) hs

theorem original_scalarValueBudget_polynomial : PolynomialBound fullInputSize
    (fun x=>scalarValueBudget (originalScalarScale x.1 x.2)):=by
  unfold scalarValueBudget
  exact (PolynomialBound.constant fullInputSize 128).mul
    (original_scalarScale_polynomial.add (PolynomialBound.constant fullInputSize 1) fullInputSize_pos)

theorem original_scalarValueBudget_originalInput : PolynomialBound PDROC.D27Prepare.Resources.size
    (fun x=>scalarValueBudget (originalScalarScale x.1 x.2)):=
  PDROC.D27Prepare.Resources.polynomial_of_fullInputSize original_scalarValueBudget_polynomial

end PDCompute.CoreSearchBudget
