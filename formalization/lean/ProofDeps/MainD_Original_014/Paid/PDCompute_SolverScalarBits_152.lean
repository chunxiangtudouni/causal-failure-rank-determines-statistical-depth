module

public import PaperProofs.Paid.PDROC_DataBits_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PDROC.DataBits

/-- The real objective block's fixed arithmetic depth. Penalty encoding
bits enter additively; this estimate is never iterated over table rows. -/
theorem solverObjective_intermediate_bits (entry : MenuEntry) (fee penalty : ℚ) (S L T : ℕ)
    (observation : ratEncodingBits entry.observation≤S) (repairs : ratEncodingBits entry.repairs≤S)
    (failure : ratEncodingBits entry.failure≤S) (feeBits : ratEncodingBits fee≤L) (penaltyBits : ratEncodingBits penalty≤T) :
    ratEncodingBits (fee*entry.repairs)≤16*(S+L+T+1) ∧
    ratEncodingBits (entry.observation+fee*entry.repairs)≤16*(S+L+T+1) ∧
    ratEncodingBits (penalty*entry.failure)≤16*(S+L+T+1) ∧
    ratEncodingBits (entry.objective fee penalty)≤16*(S+L+T+1) := by
  have first:=ratEncodingBits_mul_le fee entry.repairs
  have second:=ratEncodingBits_add_le entry.observation (fee*entry.repairs)
  have third:=ratEncodingBits_mul_le penalty entry.failure
  have fourth:=ratEncodingBits_add_le (entry.observation+fee*entry.repairs) (penalty*entry.failure)
  change ratEncodingBits (entry.objective fee penalty)≤_ at fourth
  omega

/-- Every actual new rational in original candidateCommands. Running
best is only compared/copied, so this budget has no M-fold iteration. -/
theorem solverCandidate_intermediate_bits (error charge good bad : ℚ) (L G : ℕ)
    (errorBits : ratEncodingBits error≤L) (chargeBits : ratEncodingBits charge≤L)
    (goodBits : ratEncodingBits good≤G) (badBits : ratEncodingBits bad≤G) :
    ratEncodingBits (1:ℚ)≤64*(L+G+1) ∧ ratEncodingBits (1-error)≤64*(L+G+1) ∧
    ratEncodingBits ((1-error)*good)≤64*(L+G+1) ∧ ratEncodingBits (error*bad)≤64*(L+G+1) ∧
    ratEncodingBits ((1-error)*good+error*bad)≤64*(L+G+1) ∧
    ratEncodingBits (charge+((1-error)*good+error*bad))≤64*(L+G+1) := by
  have one : ratEncodingBits (1:ℚ)=3 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have complement:=ratEncodingBits_sub_le (1:ℚ) error
  rw [one] at complement
  have goodTerm:=ratEncodingBits_mul_le (1-error) good
  have badTerm:=ratEncodingBits_mul_le error bad
  have blend:=ratEncodingBits_add_le ((1-error)*good) (error*bad)
  have score:=ratEncodingBits_add_le charge ((1-error)*good+error*bad)
  omega

end PDCompute.Solver
