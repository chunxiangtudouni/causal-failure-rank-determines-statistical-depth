module
public import PaperProofs.Structure.PA17_FullBuildWord_036c
public import PaperProofs.Structure.PA17_GivenWord_031g

/-! Complete original logical Nat/word-RAM implementation. Physical packing
and the fixed six-program generator remain separate, required A17 duties. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17NatRAM037

open IndexedRAM IndexedClosureRAM AlgorithmClaims

theorem implementation_claims :
    NatRAMImplementationClaims PA17Implementation030.constant 32 PA17Implementation030.implementation := by
  apply PA17Implementation030.natRAM_of_execution 32
  · intro q full hq hlaminar
    exact PA17FullBuildWord036c.prepared_executionClaims q full hq hlaminar
  · intro q full hq hlaminar
    dsimp only
    intro heap htable hcap hfits stage used
    exact PA17QueryWord033.prepared_executionClaims q full hq hlaminar stage used heap htable hcap hfits
  · intro q full hq hlaminar
    dsimp only
    intro used
    exact PA17GivenWord031g.prepared_executionClaims q full hq hlaminar used

theorem fullNatRAMClaims : FullNatRAMClaims :=
  ⟨PA17Implementation030.constant, 32, PA17Implementation030.implementation,
    PA17Implementation030.constant_pos, by decide, implementation_claims⟩

end PaperProofs.Structure.LaminarTree.PA17NatRAM037
