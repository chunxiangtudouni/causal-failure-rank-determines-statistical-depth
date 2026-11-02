module

public import Paid.PDROC_BitVM_Codec_FieldOps_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.FieldOps

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

/-- Complete three-getter path on arbitrary old physical work buffers.
The source is read before the target is cleared, including target=source.
Every macro is selected once; target bytes, all frames, cleanup and time
belong to that single concrete actual path. -/
theorem build (kind : Kind) (target source : Register) (value : ℚ)
    (contents : Stack → List Bool) (saved : Store)
    (sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) =
      encodeCellBits (.rational value)) :
    ∃ after : State, ∃ path : Path (program kind target source) (before contents saved) after,
      after.l = none ∧ after.var = clearedStore ∧
      after.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) = encodeCellBits (.natural (kind.value value)) ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧ after.stk 25 = [] ∧ after.stk 26 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 →
        other ≠ PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target → after.stk other = contents other) ∧
      path.states.length ≤ 512 * (RatMarshal.globalSize contents + 1) := by
  let dst := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target
  let scalar := kind.value value
  let word := encodeNatBits scalar
  let g := RatMarshal.globalSize contents
  obtain ⟨readerEnd, readPath, readPosition, readStore, rightEmpty, leftEmpty, numerator, denominator,
    originalRegs, readFrame, readTime⟩ := read_prefix kind target source value contents saved sourceCell
  have readEq : readerEnd = (⟨some (control 3), fieldStore value, readerEnd.stk⟩ : State) :=
    cfg_eq _ _ readPosition readStore rfl
  let part0 := readPath.castLast readEq
  obtain ⟨part1, size1⟩ := prepare_call kind target source value readerEnd.stk rightEmpty leftEmpty numerator denominator
  let c := Function.update readerEnd.stk 0 word
  have representation : ListBlank.mk (c 0) = ListBlank.mk
      (PaperProofs.Common.Native.RationalControllerComputation.encodeNat scalar) := by
    simp only [c, word, Function.update_self, PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral]
  obtain ⟨writerEnd, writePath, writePosition, _writerSaved, work0, work24, targetWord, writeFrame, writeTime⟩ :=
    writer_call kind target source scalar c (none, decide (value < 0)) none representation
  have writeEq : writerEnd = (⟨some (control 4), writerEnd.var, writerEnd.stk⟩ : State) :=
    cfg_eq _ _ writePosition rfl rfl
  let part2 := writePath.castLast writeEq
  obtain ⟨part3, size3⟩ := clear_call kind target source 2 writerEnd.stk writerEnd.var
  let e := Function.update writerEnd.stk 25 []
  let s : Store := ((none, writerEnd.var.1.2), writerEnd.var.2)
  obtain ⟨part4, size4⟩ := clear_call kind target source 3 e s
  let f := Function.update e 26 []
  let part5 := Path.single (finish_step kind target source f s)
  let joined := ((((part0.append part1).append part2).append part3).append part4).append part5
  have dstNot0 : dst ≠ 0 := RatMarshal.source_not_right target
  have dstNot24 : dst ≠ 24 := RatMarshal.register_not_left target
  have dstNot25 : dst ≠ (25 : Stack) := RatMarshal.register_not_temp target 0
  have dstNot26 : dst ≠ (26 : Stack) := RatMarshal.register_not_temp target 1
  have not25Dst := Ne.symm dstNot25
  have not26Dst := Ne.symm dstNot26
  have cellSize : (encodeCellBits (.rational value)).length ≤ g := by
    have bound := RatMarshal.initial_le_globalSize contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source)
    rw [sourceCell] at bound
    exact bound
  have wordSize : word.length ≤ g + 3 := (field_word_size kind value).trans (Nat.add_le_add_right cellSize 3)
  have targetBefore : c dst = contents dst := by
    dsimp only [c]
    rw [Function.update_of_ne dstNot0]
    exact originalRegs target
  have numAfter : writerEnd.stk 25 = encodeCellBits (.natural value.num.natAbs) := by
    rw [writeFrame 25 (by decide) (by decide) not25Dst]
    change (Function.update readerEnd.stk 0 word) 25 = _
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 0)]
    exact numerator
  have denAfter : writerEnd.stk 26 = encodeCellBits (.natural value.den) := by
    rw [writeFrame 26 (by decide) (by decide) not26Dst]
    change (Function.update readerEnd.stk 0 word) 26 = _
    rw [Function.update_of_ne (by decide : (26 : Stack) ≠ 0)]
    exact denominator
  have numCellSize : (encodeCellBits (.natural value.num.natAbs)).length ≤
      (encodeCellBits (.rational value)).length := by
    simp only [encodeCellBits, List.length_append, List.length_cons, List.length_nil]
    omega
  have denCellSize : (encodeCellBits (.natural value.den)).length ≤
      (encodeCellBits (.rational value)).length := by
    simp only [encodeCellBits, List.length_append, List.length_cons, List.length_nil]
    omega
  have cleanup0 : (writerEnd.stk 25).length ≤ g := by rw [numAfter]; exact numCellSize.trans cellSize
  have cleanup1 : (e 26).length ≤ g := by
    dsimp only [e]
    rw [Function.update_of_ne (by decide : (26 : Stack) ≠ 25), denAfter]
    exact denCellSize.trans cellSize
  have targetSize := RatMarshal.initial_le_globalSize contents dst
  have writerBound : writePath.states.length ≤ 128 * (g + 1) := by
    have zero : c 0 = word := Function.update_self _ _ _
    have left : c 24 = [] := by dsimp only [c]; rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 0)]; exact leftEmpty
    change writePath.states.length ≤ 32 * ((c 0).length + (c 24).length + (c dst).length + 1) at writeTime
    rw [zero, left, targetBefore] at writeTime
    simp only [List.length_nil] at writeTime
    change (contents dst).length ≤ g at targetSize
    omega
  have total : joined.states.length ≤ part0.states.length + part1.states.length + part2.states.length +
      part3.states.length + part4.states.length + 2 := by
    have first := part0.append_length part1
    have second := (part0.append part1).append_length part2
    have third := ((part0.append part1).append part2).append_length part3
    have fourth := (((part0.append part1).append part2).append part3).append_length part4
    have fifth := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    dsimp only [part5, Path.single] at first second third fourth fifth
    simp only [List.length_cons, List.length_nil] at first second third fourth fifth
    dsimp only [joined, part5, Path.single]
    omega
  have time : joined.states.length ≤ 512 * (RatMarshal.globalSize contents + 1) := by
    change part0.states.length ≤ 128 * (g + 1) at readTime
    change part1.states.length ≤ 2 * word.length + 7 at size1
    change part2.states.length ≤ 128 * (g + 1) at writerBound
    change part3.states.length = (writerEnd.stk 25).length + 2 at size3
    change part4.states.length = (e 26).length + 2 at size4
    rw [size3, size4] at total
    change joined.states.length ≤ 512 * (g + 1)
    omega
  refine ⟨(⟨none, clearedStore, f⟩ : State), joined, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, time⟩
  · change f dst = encodeCellBits (.natural scalar)
    dsimp only [f, e]
    rw [Function.update_of_ne dstNot26, Function.update_of_ne dstNot25]
    exact targetWord
  · change f 0 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (0 : Stack) ≠ 26),
      Function.update_of_ne (by decide : (0 : Stack) ≠ 25)]
    exact work0
  · change f 24 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 26),
      Function.update_of_ne (by decide : (24 : Stack) ≠ 25)]
    exact work24
  · change f 25 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 26), Function.update_self]
  · change f 26 = []
    exact Function.update_self _ _ _
  · intro other not0 not24 not25 not26 notTarget
    change f other = contents other
    dsimp only [f, e]
    rw [Function.update_of_ne not26, Function.update_of_ne not25, writeFrame other not0 not24 notTarget]
    dsimp only [c]
    rw [Function.update_of_ne not0]
    exact readFrame other not0 not24 not25 not26

end PDROC.BitVM.Codec.FieldOps
