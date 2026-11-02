module

public import Paid.PDROC_BitVM_Size_001
public import Paid.PDROC_BitVM_Log_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Size

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

/-- The actual original six-field input includes gamma and the fee's
entire rational encoding. Its physical Bool length is bounded by the
ORIGINAL variable-gamma numerical size, without any prepared fields. -/
theorem raw_input_length (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    (encodeBits (rawInput P fee)).length ≤ 24*variableGammaSize P fee := by
  have stage := PDROC.BitVM.Log.cell_word_length (.natural P.certificate.stages)
  have tools := PDROC.BitVM.Log.cell_word_length (.natural P.tools)
  have gamma := PDROC.BitVM.Log.cell_word_length (.rational P.certificate.gamma)
  have risk := PDROC.BitVM.Log.cell_word_length (.rational P.certificate.risk)
  have review := PDROC.BitVM.Log.cell_word_length (.rational P.reviewFee)
  have price := PDROC.BitVM.Log.cell_word_length (.rational fee)
  simp only [Cell.bits] at stage tools gamma risk review price
  have stageBits : natBits P.certificate.stages ≤ P.certificate.stages+1 :=
    Nat.add_le_add_right (Nat.log2_le_self _) 1
  have header : (encodeNatBits 6).length=7 := by decide
  simp only [encodeBits,rawInput,List.length_cons,List.length_nil,List.flatMap_cons,List.flatMap_nil,
    List.length_append,header]
  simp only [variableGammaSize,rawSize]
  omega

theorem variable_positive (P : PaperProofs.Paid.Parameters) (fee : ℚ) : 1 ≤ variableGammaSize P fee := by
  have positive := raw_positive P fee
  unfold variableGammaSize
  omega

theorem raw_square (P : PaperProofs.Paid.Parameters) (fee : ℚ) :
    ((encodeBits (rawInput P fee)).length+1)^2 ≤ 625*(variableGammaSize P fee)^2 := by
  have input := raw_input_length P fee
  have positive := variable_positive P fee
  have linear : (encodeBits (rawInput P fee)).length+1 ≤ 25*variableGammaSize P fee := by omega
  have squared := Nat.pow_le_pow_left linear 2
  simpa only [mul_pow,show (25 : ℕ)^2=625 from rfl] using squared

end PDROC.BitVM.Size
