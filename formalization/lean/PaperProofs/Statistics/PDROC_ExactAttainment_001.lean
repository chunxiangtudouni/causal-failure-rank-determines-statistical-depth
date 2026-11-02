module

public import PaperProofs.Statistics.PDROC_Attainment_001
public import PaperProofs.Statistics.PDROC_Mixture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Statistics.PDROC

open BinarySymmetric BinarySymmetric.Parameters

/-- D05: the concrete initial mixture attains p and g(p), and obeys MAP at
every finite stop, including both orientations of the fair zero-score tie. -/
theorem rocMAPAttains (P : Parameters) : P.RocMAPAttains :=
  rocMAPAttains_of_adjacent P (_root_.PDROC.adjacentMixtureAttains P)

/-- D05: every original e in (0,1) is attained with charge g(min(e,1-e)).
The e>1/2 branch changes only the decision of the same stopping rule. -/
theorem rocArbitraryDecisionAttains (P : Parameters) : P.RocArbitraryDecisionAttains :=
  rocArbitraryDecisionAttains_of_adjacent P (_root_.PDROC.adjacentMixtureAttains P)

end PaperProofs.Statistics.PDROC
