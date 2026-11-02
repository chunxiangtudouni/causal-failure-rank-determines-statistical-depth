module

public import PaperProofs.Paid.PDROC_DataBits_010
public import PaperProofs.Paid.PDROC_DataBits_Mixture_002
public import PaperProofs.Paid.PDROC_DataBits_Gap_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

/-- All six original data-size obligations for the fixed cached frontend.
The concrete machines and their time/space obligations remain separate. -/
theorem cachedDataBitClaims (P : Parameters) : P.CachedDataBitClaims :=
  ⟨menuBitClaims P, calibrationBitClaims, mixtureBitClaims, positiveGapBitClaims P,
    fixedGammaPolynomialData P.certificate.gamma, variableGammaPolynomialData⟩

end PDROC.DataBits
