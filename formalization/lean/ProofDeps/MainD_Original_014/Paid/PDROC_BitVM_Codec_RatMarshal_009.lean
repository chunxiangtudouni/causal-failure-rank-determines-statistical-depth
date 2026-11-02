module

public import Paid.PDROC_BitVM_Codec_RatMarshal_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.RatMarshal

open Turing PDROC.BitVM.Native
open PaperProofs.Paid.Computation

/-- These roles and code are static. The mathematical Rat merely describes
the canonical source bytes; neither it nor its two Nat fields enters code. -/
def before (contents : Stack → List Bool) (store : Store) : State := ⟨some 0, store, contents⟩

def inputSize (source : Register) (num den : Fin 7) (contents : Stack → List Bool) : ℕ :=
  (contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source)).length +
    (contents (tempSlot num)).length + (contents (tempSlot den)).length

theorem temp_ne_temp (num den : Fin 7) (different : num ≠ den) : tempSlot num ≠ tempSlot den :=
  fun same => different (tempSlot_injective same)

/-- Copy, two genuine clears, actual tag/sign reads, two genuine Header
scans and two real drains all belong to ONE path ending at real HALT.
No prepared operand tape, sign oracle, widths or old-target initialization
is assumed. Native work emptiness is the actual Ready/Clear invariant. -/
theorem build (source : Register) (num den : Fin 7) (different : num ≠ den)
    (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) =
      encodeCellBits (.rational value))
    (rightEmpty : contents 0 = []) (leftEmpty : contents 24 = []) :
    ∃ after : State, ∃ path : Trace (program source num den different) (before contents store) after,
      after.l = none ∧ after.var = (none, decide (value < 0)) ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧
      after.stk (tempSlot num) = encodeCellBits (.natural value.num.natAbs) ∧
      after.stk (tempSlot den) = encodeCellBits (.natural value.den) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ tempSlot num → other ≠ tempSlot den →
        after.stk other = contents other) ∧
      path.states.length ≤ 32 * (inputSize source num den contents + 1) := by
  let sign := decide (value < 0)
  let numWord := encodeNatBits value.num.natAbs
  let denWord := encodeNatBits value.den
  let word := encodeCellBits (.rational value)
  let a := Function.update contents 0 word
  let b := Function.update a (tempSlot num) []
  let c := Function.update b (tempSlot den) []
  let d := Function.update c 0 (numWord ++ denWord)
  let e := Function.update (Function.update d 0 denWord) 24 numWord.reverse
  let f := Function.update (Function.update e 24 []) (tempSlot num) (false :: numWord.reverse.reverse)
  let g := Function.update (Function.update f 0 []) 24 denWord.reverse
  let h := Function.update (Function.update g 24 []) (tempSlot den) (false :: denWord.reverse.reverse)
  have numNot0 := temp_not_right num
  have numNot24 := temp_not_left num
  have denNot0 := temp_not_right den
  have denNot24 := temp_not_left den
  have numNotDen := temp_ne_temp num den different
  have zeroNotNum := Ne.symm numNot0
  have leftNotNum := Ne.symm numNot24
  have zeroNotDen := Ne.symm denNot0
  have leftNotDen := Ne.symm denNot24
  have denNotNum := Ne.symm numNotDen
  let part0 := Trace.single (reset_step source num den different contents store)
  obtain ⟨part1, size1⟩ := copy_call source num den different contents word sourceCell rightEmpty leftEmpty
  obtain ⟨part2, size2⟩ := clear_call (program source num den different) 4 5 num
    (by intro label; cases label; rfl) a false
  obtain ⟨part3, size3⟩ := clear_call (program source num den different) 5 6 den
    (by intro label; cases label; rfl) b false
  have tagInput : c 0 = true :: sign :: (numWord ++ denWord) := by
    change c 0 = word
    dsimp only [c, b, a]
    rw [Function.update_of_ne (Ne.symm denNot0), Function.update_of_ne (Ne.symm numNot0),
      Function.update_self]
  let part4 := Trace.single (tag_step source num den different c (numWord ++ denWord) sign (none, false) tagInput)
  obtain ⟨part5, size5⟩ := header_call (program source num den different) numeratorLabels 11 num
    (numerator_agrees source num den different) d value.num.natAbs denWord sign rfl
    (by dsimp only [d, c, b, a]; simp_all)
    (by dsimp only [d, c, b, a]; simp_all)
  obtain ⟨part6, size6⟩ := drain_call (program source num den different) 11 12
    (numeratorDrainEmbedding num den different) (drain_num_agrees source num den different) e numWord.reverse sign
    (by change e (tempSlot den) = []; dsimp only [e, d, c, b, a]; simp_all)
    (by change e 24 = numWord.reverse; dsimp only [e]; exact Function.update_self _ _ _)
    (by change e (tempSlot num) = []; dsimp only [e, d, c, b, a]; simp_all)
  obtain ⟨part7, size7⟩ := header_call (program source num den different) denominatorLabels 16 den
    (denominator_agrees source num den different) f value.den [] sign
    (by dsimp only [f, e, denWord]; simp_all)
    (by dsimp only [f, e, d, c, b, a]; simp_all)
    (by dsimp only [f]; simp_all)
  obtain ⟨part8, size8⟩ := drain_call (program source num den different) 16 17
    (denominatorDrainEmbedding den) (drain_den_agrees source num den different) g denWord.reverse sign
    (by change g 0 = []; dsimp only [g]; simp_all)
    (by change g 24 = denWord.reverse; dsimp only [g]; exact Function.update_self _ _ _)
    (by change g (tempSlot den) = []; dsimp only [g, f, e, d, c, b, a]; simp_all)
  let part9 := Trace.single (halt_step source num den different h (none, sign))
  let joined := ((((((((part0.append part1).append part2).append part3).append part4).append part5).append
    part6).append part7).append part8).append part9
  have total : joined.states.length ≤ 2 + part1.states.length + part2.states.length +
      part3.states.length + 2 + part5.states.length + part6.states.length + part7.states.length +
      part8.states.length + 2 := by
    have first := part0.append_length part1
    have second := (part0.append part1).append_length part2
    have third := ((part0.append part1).append part2).append_length part3
    have fourth := (((part0.append part1).append part2).append part3).append_length part4
    have fifth := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    have sixth := (((((part0.append part1).append part2).append part3).append part4).append part5).append_length part6
    have seventh := ((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append_length part7
    have eighth := (((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append part7).append_length part8
    have ninth := ((((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append part7).append part8).append_length part9
    dsimp only [part0, part4, part9, Trace.single] at first second third fourth fifth sixth seventh eighth ninth
    simp only [List.length_cons, List.length_nil] at first second third fourth fifth sixth seventh eighth ninth
    dsimp only [joined, part0, part4, part9, Trace.single]
    omega
  have oldNum : (a (tempSlot num)).length = (contents (tempSlot num)).length := by
    dsimp only [a]
    rw [Function.update_of_ne numNot0]
  have oldDen : (b (tempSlot den)).length = (contents (tempSlot den)).length := by
    dsimp only [b, a]
    simp_all
  have wordLength : word.length = 2 + numWord.length + denWord.length := by
    simp only [word, encodeCellBits, List.length_append, List.length_cons, List.length_nil, numWord, denWord]
  have numLength : numWord.length = 2 * PaperProofs.Paid.Parameters.natBits value.num.natAbs + 1 := by
    simp [numWord, encodeNatBits]
    omega
  have denLength : denWord.length = 2 * PaperProofs.Paid.Parameters.natBits value.den + 1 := by
    simp [denWord, encodeNatBits]
    omega
  have time : joined.states.length ≤ 32 * (inputSize source num den contents + 1) := by
    rw [size1, size2, size3, size5, size6, size7, size8, oldNum, oldDen,
      List.length_reverse, List.length_reverse] at total
    have actualWord := congrArg List.length sourceCell
    change (contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source)).length = word.length at actualWord
    dsimp only [inputSize]
    omega
  refine ⟨(⟨none, (none, sign), h⟩ : State), joined, rfl, rfl, ?_, ?_, ?_, ?_, ?_, time⟩
  · change h 0 = []
    dsimp only [h, g, f, e, d, c, b, a]
    simp_all
  · change h 24 = []
    dsimp only [h, g, f, e, d, c, b, a]
    simp_all
  · change h (tempSlot num) = encodeCellBits (.natural value.num.natAbs)
    dsimp only [h, g, f, e, d, c, b, a]
    simp_all [numWord, encodeCellBits]
  · change h (tempSlot den) = encodeCellBits (.natural value.den)
    dsimp only [h]
    simp only [Function.update_self, List.reverse_reverse]
    rfl
  · intro other not0 not24 notNum notDen
    change h other = contents other
    dsimp only [h, g, f, e, d, c, b, a]
    simp_all

end PDROC.BitVM.Codec.RatMarshal
