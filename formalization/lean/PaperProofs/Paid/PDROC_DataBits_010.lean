module

public import PaperProofs.Paid.PDROC_DataBits_009
public import PaperProofs.Paid.PDROC_DataBits_Counts_003
public import PaperProofs.Paid.PDROC_DataBits_Search_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

abbrev DataInput := Parameters × ℚ

def fullInputSize (x : DataInput) : ℕ :=
  x.1.certificate.stages + ratEncodingBits x.1.certificate.gamma +
    ratEncodingBits x.1.certificate.risk + ratEncodingBits x.1.reviewFee + ratEncodingBits x.2 +
      ⌈x.1.certificate.gamma⁻¹⌉₊ + 1

theorem fullInputSize_pos (x : DataInput) : 1 ≤ fullInputSize x := by
  unfold fullInputSize
  omega

theorem numericalSize_polynomial : PolynomialBound fullInputSize (fun x => x.1.numericalSize x.2) := by
  have hs := fullInputSize_pos
  have hbase := PolynomialBound.size fullInputSize
  have hN : PolynomialBound fullInputSize (fun x => x.1.certificate.stages) :=
    hbase.mono (by intro x; dsimp [fullInputSize]; omega)
  have hG : PolynomialBound fullInputSize (fun x => ratEncodingBits x.1.certificate.gamma) :=
    hbase.mono (by intro x; dsimp [fullInputSize]; omega)
  have hD : PolynomialBound fullInputSize (fun x => ratEncodingBits x.1.certificate.risk) :=
    hbase.mono (by intro x; dsimp [fullInputSize]; omega)
  have hC : PolynomialBound fullInputSize (fun x => ratEncodingBits x.1.reviewFee) :=
    hbase.mono (by intro x; dsimp [fullInputSize]; omega)
  have hF : PolynomialBound fullInputSize (fun x => ratEncodingBits x.2) :=
    hbase.mono (by intro x; dsimp [fullInputSize]; omega)
  have hK : PolynomialBound fullInputSize (fun x => x.1.tools) :=
    hN.mono (by intro x; exact (x.1.tools_lt_stages).le)
  obtain ⟨C, degree, hCpos, hcounts⟩ := certificate_counts_polynomial
  have hCounts : PolynomialBound fullInputSize
      (fun x => x.1.certificate.t0+x.1.certificate.M+x.1.certificate.E+x.1.certificate.Q) := by
    refine ⟨C, degree, hCpos, ?_⟩
    intro x
    have hsize : dataInputSize x.1.certificate ≤ fullInputSize x := by
      dsimp [dataInputSize, fullInputSize]
      omega
    exact (hcounts x.1.certificate).trans
      (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hsize degree))
  have hT : PolynomialBound fullInputSize (fun x => x.1.certificate.t0) :=
    hCounts.mono (by intro x; omega)
  have hM : PolynomialBound fullInputSize (fun x => x.1.certificate.M) :=
    hCounts.mono (by intro x; omega)
  have hQ : PolynomialBound fullInputSize (fun x => x.1.certificate.Q) :=
    hCounts.mono (by intro x; omega)
  have hbT := PolynomialBound.natBits hs hT
  have hbM := PolynomialBound.natBits hs hM
  have hbN := PolynomialBound.natBits hs hN
  let c (n : ℕ) := PolynomialBound.constant fullInputSize n
  have hJ : PolynomialBound fullInputSize (fun x => x.1.bisectionBudget x.2) := by
    apply ((c 64).mul (((((hN.add hD hs).add hC hs).add hF hs).add hbT hs).add (c 1) hs)).mono
    intro x
    exact bisectionBudget_bit_bound x.1 x.2
  have hLambda : PolynomialBound fullInputSize (fun x => ratEncodingBits x.1.Lambda) := by
    apply (((((hC.add hD hs).add hN hs).add hbT hs).add (c 10) hs)).mono
    intro x
    exact Lambda_encoding x.1
  have hL : PolynomialBound fullInputSize (fun x => menuEncodingSize x.1 x.2) := by
    change PolynomialBound fullInputSize (fun x => 512*(x.1.certificate.Q+1)*
      (ratEncodingBits x.1.certificate.gamma + ratEncodingBits x.1.reviewFee +
        ratEncodingBits x.2 + natBits x.1.certificate.M + 2))
    exact ((c 512).mul (hQ.add (c 1) hs)).mul ((((hG.add hC hs).add hF hs).add hbM hs).add (c 2) hs)
  have hA : PolynomialBound fullInputSize (fun x => 2*(x.1.certificate.M+1)+2) :=
    ((c 2).mul (hM.add (c 1) hs)).add (c 2) hs
  have hB := ((hN.add (c 1) hs).mul hA).mul hL
  have hR := (c 64).mul ((((hC.add hG hs).add hbM hs).add hbN hs).add (c 1) hs)
  have hEntry : PolynomialBound fullInputSize (fun x => menuEntrySizeBound x.1 (menuEncodingSize x.1 x.2)) := by
    change PolynomialBound fullInputSize (fun x => 3+natBits x.1.certificate.M+3*
      (2*((x.1.certificate.stages+1)*(2*(x.1.certificate.M+1)+2)*menuEncodingSize x.1 x.2)+
        64*(ratEncodingBits x.1.reviewFee+ratEncodingBits x.1.certificate.gamma+
          natBits x.1.certificate.M+natBits x.1.certificate.stages+1)+2))
    exact ((c 3).add hbM hs).add ((c 3).mul ((((c 2).mul hB).add hR hs).add (c 2) hs)) hs
  have hTable : PolynomialBound fullInputSize
      (fun x => menuTableSizeBound x.1 (menuEncodingSize x.1 x.2)) := by
    exact ((hN.add (c 1) hs).mul (hK.add (c 1) hs)).mul hEntry
  have hSolution : PolynomialBound fullInputSize
      (fun x => searchSolutionSizeBound x.1 (menuEncodingSize x.1 x.2) (x.1.bisectionBudget x.2)) := by
    exact ((c 8).mul ((hJ.add hLambda hs).add (c 1) hs)).add hTable hs
  have hUpper : PolynomialBound fullInputSize (fun x => numericalSizeBound x.1 x.2) := by
    have hFirst := (((hT.add hM hs).add hQ hs).add hJ hs).add
      ((hM.add (c 1) hs).mul ((c 2).mul hL)) hs
    have hSecond := (hM.add (c 1) hs).mul
      (((c 512).mul (hQ.add (c 1) hs)).mul (hG.add (c 2) hs))
    exact (hFirst.add hSecond hs).add ((c 1).add ((c 2).mul hSolution) hs) hs
  exact hUpper.mono (fun x => numericalSize_le_bound x.1 x.2)

theorem variableGammaPolynomialData : VariableGammaPolynomialData := by
  obtain ⟨C, degree, hC, h⟩ := numericalSize_polynomial
  exact ⟨C, degree, hC, fun P fee _hfee => h (P,fee)⟩

theorem fixedGammaPolynomialData (gamma : ℚ) : FixedGammaPolynomialData gamma :=
  fixedGammaPolynomialData_of_variable gamma variableGammaPolynomialData

end PDROC.DataBits
