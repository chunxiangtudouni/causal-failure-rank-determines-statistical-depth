module

public import Paid.PDROC_BitVM_Codec_NatCast_025
public import Paid.PDROC_BitVM_Codec_FieldOps_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCast

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Codec.FieldOps (Path cfg_eq)

theorem build (target source : Register) (value : ℕ) (contents : Stack → List Bool) (saved : Store)
    (sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) = encodeCellBits (.natural value)) :
    ∃ after : State, ∃ path : Path (program target source) (before contents saved) after,
      after.l = none ∧ after.var = FieldOps.clearedStore ∧
      after.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) = encodeCellBits (.rational value) ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧ after.stk 25 = [] ∧ after.stk 26 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 →
        other ≠ PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target → after.stk other = contents other) ∧
      path.states.length ≤ 512 * (RatMarshal.globalSize contents + 1) := by
  let dst := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target
  let word := encodeNatBits value
  let g := RatMarshal.globalSize contents
  let a := Function.update contents 0 []
  let b := Function.update a 24 []
  let c := Function.update b 0 word
  let part0 := Path.single (reset_step target source contents saved)
  obtain ⟨part1, size1⟩ := clear_call target source 0 contents FieldOps.clearedStore
  obtain ⟨part2, size2⟩ := clear_call target source 1 a FieldOps.clearedStore
  have sourceCurrent : b (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) = encodeCellBits (.natural value) := by
    dsimp only [b, a]
    rw [Function.update_of_ne (RatMarshal.register_not_left source),
      Function.update_of_ne (RatMarshal.source_not_right source)]
    exact sourceCell
  obtain ⟨part3, size3⟩ := marshal_call target source value b (none, false) none sourceCurrent
    (by simp [b, a]) (by simp [b, a])
  have representation : ListBlank.mk (c 0) = ListBlank.mk
      (PaperProofs.Common.Native.RationalControllerComputation.encodeNat value) := by
    simp only [c, word, Function.update_self, PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral]
  obtain ⟨writerEnd, writePath, writePosition, writeSaved, work0, work24, num, writeFrame, writeTime⟩ :=
    writer_call target source value c (none, false) none representation
  have writeEq : writerEnd = (⟨some (control 3), writerEnd.var, writerEnd.stk⟩ : State) :=
    cfg_eq _ _ writePosition rfl rfl
  let part4 := writePath.castLast writeEq
  obtain ⟨literalPath, literalTime⟩ := literal_call target source writerEnd.stk writerEnd.var work24
  have signFalse : writerEnd.var.1.2 = false := congrArg Prod.snd writeSaved
  let d := Function.update writerEnd.stk 26 one
  have literalEq : (⟨some (assemblerLabels 0), ((none, writerEnd.var.1.2), writerEnd.var.2), d⟩ : State) =
      (⟨some (assemblerLabels 0), ((none, false), writerEnd.var.2), d⟩ : State) := by rw [signFalse]
  let part5 := literalPath.castLast literalEq
  have numAtEntry : d 25 = encodeCellBits (.natural value) := by
    dsimp only [d]
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 26)]
    exact num
  have denAtEntry : d 26 = one := Function.update_self _ _ _
  obtain ⟨assembled, assemblePath, assemblePosition, _assembleSaved, targetWord, scratch, right,
    assembleFrame, assembleTime⟩ := assembler_call target source value d none writerEnd.var.2 numAtEntry denAtEntry
  have assembleEq : assembled = (⟨some (control 4), assembled.var, assembled.stk⟩ : State) :=
    cfg_eq _ _ assemblePosition rfl rfl
  let part6 := assemblePath.castLast assembleEq
  obtain ⟨part7, size7⟩ := clear_call target source 2 assembled.stk assembled.var
  let e := Function.update assembled.stk 25 []
  let s : Store := ((none, assembled.var.1.2), assembled.var.2)
  obtain ⟨part8, size8⟩ := clear_call target source 3 e s
  let f := Function.update e 26 []
  let part9 := Path.single (finish_step target source f s)
  let joined := ((((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append
    part7).append part8).append part9
  have dstNot0 : dst ≠ 0 := RatMarshal.source_not_right target
  have dstNot24 : dst ≠ 24 := RatMarshal.register_not_left target
  have dstNot25 : dst ≠ (25 : Stack) := RatMarshal.register_not_temp target 0
  have dstNot26 : dst ≠ (26 : Stack) := RatMarshal.register_not_temp target 1
  have initial0 := RatMarshal.initial_le_globalSize contents 0
  have initial24 := RatMarshal.initial_le_globalSize contents 24
  have initial25 := RatMarshal.initial_le_globalSize contents 25
  have initial26 := RatMarshal.initial_le_globalSize contents 26
  have initialTarget := RatMarshal.initial_le_globalSize contents dst
  have sourceSize : (encodeCellBits (.natural value)).length ≤ g := by
    have bound := RatMarshal.initial_le_globalSize contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source)
    rw [sourceCell] at bound
    exact bound
  have wordSize : word.length ≤ g := by
    change (false :: word).length ≤ g at sourceSize
    simp only [List.length_cons] at sourceSize
    omega
  have targetBefore : c dst = contents dst := by
    dsimp only [c, b, a]
    rw [Function.update_of_ne dstNot0, Function.update_of_ne dstNot24, Function.update_of_ne dstNot0]
  have old25 : c 25 = contents 25 := by simp [c, b, a]
  have old26 : c 26 = contents 26 := by simp [c, b, a]
  have oldTargetWriter : writerEnd.stk dst = contents dst :=
    (writeFrame dst dstNot0 dstNot24 dstNot25).trans targetBefore
  have literal26 : writerEnd.stk 26 = contents 26 :=
    (writeFrame 26 (by decide) (by decide) (by decide)).trans old26
  have dTarget : d dst = contents dst := by
    dsimp only [d]
    rw [Function.update_of_ne dstNot26]
    exact oldTargetWriter
  have d24 : d 24 = [] := by
    dsimp only [d]
    rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 26)]
    exact work24
  have d0 : d 0 = [] := by
    dsimp only [d]
    rw [Function.update_of_ne (by decide : (0 : Stack) ≠ 26)]
    exact work0
  have oneSize : one.length = 4 := by decide
  have assemblerBound : assemblePath.states.length ≤ 160 * (g + 1) := by
    change assemblePath.states.length ≤ 32 * ((d 24).length + (d dst).length + (d 25).length + (d 26).length + 1) at assembleTime
    rw [d24, dTarget, numAtEntry, denAtEntry, oneSize] at assembleTime
    simp only [List.length_nil] at assembleTime
    change (contents dst).length ≤ g at initialTarget
    omega
  have writerBound : writePath.states.length ≤ 64 * (g + 1) := by
    have c0 : c 0 = word := Function.update_self _ _ _
    have c24 : c 24 = [] := by simp [c, b, a]
    rw [c0, c24, old25] at writeTime
    simp only [List.length_nil] at writeTime
    change (contents 25).length ≤ g at initial25
    omega
  have cleanup25 : (assembled.stk 25).length ≤ g := by
    rw [assembleFrame 25 (Ne.symm dstNot25) (by decide), numAtEntry]
    exact sourceSize
  have cleanup26 : (e 26).length = 4 := by
    dsimp only [e]
    rw [Function.update_of_ne (by decide : (26 : Stack) ≠ 25),
      assembleFrame 26 (Ne.symm dstNot26) (by decide), denAtEntry, oneSize]
  have total : joined.states.length ≤ 2 + part1.states.length + part2.states.length + part3.states.length +
      part4.states.length + part5.states.length + part6.states.length + part7.states.length + part8.states.length + 2 := by
    have first := part0.append_length part1
    have second := (part0.append part1).append_length part2
    have third := ((part0.append part1).append part2).append_length part3
    have fourth := (((part0.append part1).append part2).append part3).append_length part4
    have fifth := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    have sixth := (((((part0.append part1).append part2).append part3).append part4).append part5).append_length part6
    have seventh := ((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append_length part7
    have eighth := (((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append part7).append_length part8
    have ninth := ((((((((part0.append part1).append part2).append part3).append part4).append part5).append part6).append part7).append part8).append_length part9
    dsimp only [part0, part9, Path.single] at first second third fourth fifth sixth seventh eighth ninth
    simp only [List.length_cons, List.length_nil] at first second third fourth fifth sixth seventh eighth ninth
    dsimp only [joined, part0, part9, Path.single]
    omega
  have time : joined.states.length ≤ 512 * (RatMarshal.globalSize contents + 1) := by
    change part1.states.length = (contents 0).length + 2 at size1
    change part2.states.length = (a 24).length + 2 at size2
    have same24 : a 24 = contents 24 := by simp [a]
    rw [same24] at size2
    change part3.states.length = 2 * word.length + 5 at size3
    change part4.states.length ≤ 64 * (g + 1) at writerBound
    change part5.states.length = (writerEnd.stk 26).length + 2 at literalTime
    rw [literal26] at literalTime
    change part6.states.length ≤ 160 * (g + 1) at assemblerBound
    change part7.states.length = (assembled.stk 25).length + 2 at size7
    change part8.states.length = (e 26).length + 2 at size8
    rw [size1, size2, size3, literalTime, size7, size8, cleanup26] at total
    change (contents 0).length ≤ g at initial0
    change (contents 24).length ≤ g at initial24
    change (contents 26).length ≤ g at initial26
    change joined.states.length ≤ 512 * (g + 1)
    omega
  refine ⟨(⟨none, FieldOps.clearedStore, f⟩ : State), joined, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, time⟩
  · change f dst = encodeCellBits (.rational value)
    dsimp only [f, e]
    rw [Function.update_of_ne dstNot26, Function.update_of_ne dstNot25]
    exact targetWord
  · change f 0 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (0 : Stack) ≠ 26), Function.update_of_ne (by decide : (0 : Stack) ≠ 25), right]
    exact d0
  · change f 24 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 26), Function.update_of_ne (by decide : (24 : Stack) ≠ 25)]
    exact scratch
  · change f 25 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 26), Function.update_self]
  · change f 26 = []
    exact Function.update_self _ _ _
  · intro other not0 not24 not25 not26 notTarget
    change f other = contents other
    dsimp only [f, e]
    rw [Function.update_of_ne not26, Function.update_of_ne not25, assembleFrame other notTarget not24]
    dsimp only [d]
    rw [Function.update_of_ne not26, writeFrame other not0 not24 not25]
    dsimp only [c, b, a]
    rw [Function.update_of_ne not0, Function.update_of_ne not24, Function.update_of_ne not0]

end PDROC.BitVM.Codec.NatCast
