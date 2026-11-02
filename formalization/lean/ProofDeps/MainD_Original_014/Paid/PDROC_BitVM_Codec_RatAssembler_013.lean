module

public import Paid.PDROC_BitVM_Codec_RatAssembler_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.RatAssembler

open Turing PDROC.BitVM.Native

def before (contents : Stack → List Bool) (saved : Option Bool) (sign : Bool) : State :=
  ⟨some 0, (saved, sign), contents⟩

def inputSize (target : Register) (num den : Fin 7) (contents : Stack → List Bool) : ℕ :=
  (contents 24).length + (contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target)).length +
    (contents (RatMarshal.tempSlot num)).length + (contents (RatMarshal.tempSlot den)).length

theorem target_not_left (target : Register) :
    PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target ≠ 24 := by
  intro same
  have values := congrArg Fin.val same
  have bounds := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_bounds target
  change (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target).val = 24 at values
  omega

theorem temp_not_target (temp : Fin 7) (target : Register) :
    RatMarshal.tempSlot temp ≠ PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target := by
  intro same
  have values := congrArg Fin.val same
  have tempBound := RatMarshal.tempSlot_bounds temp
  have targetBounds := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_bounds target
  omega

/-- Entire real assembler path. Words are proof descriptions of the
already-produced source Nat Cells, never data passed into program control.
Both old target and old native LEFT may be arbitrary physical lists.
Native-right0 and all other unselected roles are literally retained. -/
theorem build (target : Register) (num den : Fin 7) (numWord denWord : List Bool)
    (contents : Stack → List Bool) (saved : Option Bool) (sign : Bool)
    (numerator : contents (RatMarshal.tempSlot num) = false :: numWord)
    (denominator : contents (RatMarshal.tempSlot den) = false :: denWord) :
    ∃ after : State, ∃ path : RatMarshal.Trace (program target num den) (before contents saved sign) after,
      after.l = none ∧ after.var = (none, sign) ∧
      after.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) = true :: sign :: (numWord ++ denWord) ∧
      after.stk 24 = [] ∧
      (∀ other, other ≠ PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target → other ≠ 24 →
        after.stk other = contents other) ∧
      path.states.length ≤ 32 * (inputSize target num den contents + 1) := by
  let dst := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target
  let a := Function.update contents 24 []
  let b := Function.update a dst []
  let c := Function.update b dst (denWord ++ b dst)
  let d := Function.update c dst (numWord ++ c dst)
  let e := Function.update d dst (true :: sign :: d dst)
  have dstNot24 : dst ≠ 24 := target_not_left target
  have leftNotDst := Ne.symm dstNot24
  have numNotDst : RatMarshal.tempSlot num ≠ dst := temp_not_target num target
  have denNotDst : RatMarshal.tempSlot den ≠ dst := temp_not_target den target
  have numNot24 := RatMarshal.temp_not_left num
  have denNot24 := RatMarshal.temp_not_left den
  obtain ⟨part0, size0⟩ := clear_call (program target num den) 0 1 (embedding den target) 2
    (clear_left_agrees target num den) contents saved sign
  obtain ⟨part1, size1⟩ := clear_call (program target num den) 1 2 (embedding den target) 1
    (clear_target_agrees target num den) a none sign
  obtain ⟨part2, size2⟩ := nat_call (program target num den) denominatorLabels 7 den target
    (denominator_agrees target num den) b denWord sign
    (by dsimp only [b, a]; simp_all)
    (by dsimp only [b, a]; simp_all)
  obtain ⟨part3, size3⟩ := nat_call (program target num den) numeratorLabels 12 num target
    (numerator_agrees target num den) c numWord sign
    (by dsimp only [c, b, a]; simp_all)
    (by dsimp only [c, b, a]; simp_all)
  let part4 := RatMarshal.Trace.single (tag_step target num den d none sign)
  let joined := (((part0.append part1).append part2).append part3).append part4
  have total : joined.states.length ≤ part0.states.length + part1.states.length +
      part2.states.length + part3.states.length + 2 := by
    have first := part0.append_length part1
    have second := (part0.append part1).append_length part2
    have third := ((part0.append part1).append part2).append_length part3
    have fourth := (((part0.append part1).append part2).append part3).append_length part4
    dsimp only [part4, RatMarshal.Trace.single] at first second third fourth
    simp only [List.length_cons, List.length_nil] at first second third fourth
    dsimp only [joined, part4, RatMarshal.Trace.single]
    omega
  have oldTarget : (a dst).length = (contents dst).length := by
    dsimp only [a]
    rw [Function.update_of_ne dstNot24]
  have numSize := congrArg List.length numerator
  have denSize := congrArg List.length denominator
  simp only [List.length_cons] at numSize denSize
  have time : joined.states.length ≤ 32 * (inputSize target num den contents + 1) := by
    change part0.states.length = (contents 24).length + 2 at size0
    change part1.states.length = (a dst).length + 2 at size1
    rw [size0, size1, size2, size3, oldTarget] at total
    change joined.states.length ≤ 32 * ((contents 24).length + (contents dst).length +
      (contents (RatMarshal.tempSlot num)).length + (contents (RatMarshal.tempSlot den)).length + 1)
    omega
  refine ⟨(⟨none, (none, sign), e⟩ : State), joined, rfl, rfl, ?_, ?_, ?_, time⟩
  · change e dst = true :: sign :: (numWord ++ denWord)
    simp only [e, d, c, b, Function.update_self, List.append_nil]
  · change e 24 = []
    dsimp only [e, d, c, b, a]
    simp_all
  · intro other notDst not24
    change other ≠ dst at notDst
    change e other = contents other
    dsimp only [e, d, c, b, a]
    simp_all

end PDROC.BitVM.Codec.RatAssembler
