module

public import Paid.PDROC_BitVM_Codec_FieldOps_018

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.FieldOps

open Turing PaperProofs.Paid.Computation

def Path.castLast {Λ σ : Type} {machine : Λ → TM2.Stmt Alphabet Λ σ}
    {before after final : TM2.Cfg Alphabet Λ σ} (path : Path machine before after) (same : after = final) :
    Path machine before final where
  states := path.states
  first := path.first
  actual := path.actual
  last := path.last.trans (congrArg some same)

theorem cfg_eq (left right : State) (position : left.l = right.l)
    (saved : left.var = right.var) (data : left.stk = right.stk) : left = right := by
  rcases left with ⟨a, b, c⟩
  rcases right with ⟨d, e, f⟩
  change a = d at position
  change b = e at saved
  change c = f at data
  subst d
  subst e
  subst f
  rfl

/-- A proof description of the state ACTUALLY produced by reader_call,
never an initialization instruction which supplies the mathematical sign. -/
def fieldStore (value : ℚ) : Store := ((none, decide (value < 0)), (none, ()))

/-- After the same concrete reader: actual selected field copying or
three actual Bool writes for the negative result, then the true writer
entry. No host decode/Kind.value evaluation occurs in program. -/
theorem prepare_call (kind : Kind) (target source : Register) (value : ℚ)
    (contents : Stack → List Bool) (rightEmpty : contents 0 = []) (leftEmpty : contents 24 = [])
    (numerator : contents 25 = encodeCellBits (.natural value.num.natAbs))
    (denominator : contents 26 = encodeCellBits (.natural value.den)) :
    ∃ path : Path (program kind target source)
      (⟨some (control 3), fieldStore value, contents⟩ : State)
      (⟨some (writerLabels 0), fieldStore value,
        Function.update contents 0 (encodeNatBits (kind.value value))⟩ : State),
      path.states.length ≤ 2 * (encodeNatBits (kind.value value)).length + 7 := by
  by_cases isNegative : kind = .negative
  · subst kind
    have valueEq : Kind.value .negative value = if decide (value < 0) then 1 else 0 := by
      by_cases below : value < 0 <;> simp [Kind.value, below]
    have words : [true, false, decide (value < 0)] = encodeNatBits (Kind.value .negative value) := by
      rw [valueEq]
      exact (bool_word (decide (value < 0))).symm
    let actual := Path.single (negative_step target source contents (fieldStore value) rightEmpty)
    have finalEq : (⟨some (writerLabels 0), fieldStore value,
        Function.update contents 0 [true, false, (fieldStore value).1.2]⟩ : State) =
        (⟨some (writerLabels 0), fieldStore value,
          Function.update contents 0 (encodeNatBits (Kind.value .negative value))⟩ : State) := by
      change (⟨some (writerLabels 0), fieldStore value,
        Function.update contents 0 [true, false, decide (value < 0)]⟩ : State) = _
      rw [words]
    refine ⟨actual.castLast finalEq, ?_⟩
    change 2 ≤ 2 * (encodeNatBits (Kind.value .negative value)).length + 7
    omega
  · have sourceCell : contents (RatMarshal.tempSlot (selectedTemp kind)) =
        encodeCellBits (.natural (kind.value value)) := by
      cases kind with
      | numeratorAbs => exact numerator
      | denominator => exact denominator
      | negative => exact False.elim (isNegative rfl)
    let first := Path.single (field_step kind target source isNegative contents (fieldStore value))
    obtain ⟨second, size⟩ := marshal_call kind target source (kind.value value) contents
      (none, decide (value < 0)) none sourceCell rightEmpty leftEmpty
    let joined := first.append second
    refine ⟨joined, ?_⟩
    have total := first.append_length second
    dsimp only [first, Path.single] at total
    simp only [List.length_cons, List.length_nil, size] at total
    dsimp only [joined, first, Path.single]
    omega

/-- Byte-size arithmetic only: it is used to bound the same real path,
not provided as a width/fuel/answer parameter to the machine. -/
theorem field_word_size (kind : Kind) (value : ℚ) :
    (encodeNatBits (kind.value value)).length ≤ (encodeCellBits (.rational value)).length + 3 := by
  cases kind with
  | numeratorAbs =>
    simp only [Kind.value, encodeCellBits, List.length_append, List.length_cons, List.length_nil]
    omega
  | denominator =>
    simp only [Kind.value, encodeCellBits, List.length_append, List.length_cons, List.length_nil]
    omega
  | negative =>
    by_cases below : value < 0
    · simp only [Kind.value, ite_eq_left below]
      change 3 ≤ (encodeCellBits (.rational value)).length + 3
      omega
    · simp only [Kind.value, ite_eq_right below]
      change 3 ≤ (encodeCellBits (.rational value)).length + 3
      omega

end PDROC.BitVM.Codec.FieldOps
