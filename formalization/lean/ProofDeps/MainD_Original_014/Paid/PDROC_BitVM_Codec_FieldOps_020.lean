module

public import Paid.PDROC_BitVM_Codec_FieldOps_019

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.FieldOps

open Turing PaperProofs.Paid.Computation

def prefixContents (contents : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update contents 0 []) 24 []

theorem prefix_register (contents : Stack → List Bool) (reg : Register) :
    prefixContents contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg) =
      contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg) := by
  dsimp only [prefixContents]
  rw [Function.update_of_ne (RatMarshal.register_not_left reg),
    Function.update_of_ne (RatMarshal.source_not_right reg)]

theorem prefix_25 (contents : Stack → List Bool) : prefixContents contents 25 = contents 25 := by
  simp [prefixContents]

theorem prefix_26 (contents : Stack → List Bool) : prefixContents contents 26 = contents 26 := by
  simp [prefixContents]

/-- Actual entry reset and both work clears PRODUCE the real reader entry.
The reader's whole path is selected once and appended at that exact state.
There is no caller-empty workspace, prepared field tape or sign premise. -/
theorem read_prefix (kind : Kind) (target source : Register) (value : ℚ)
    (contents : Stack → List Bool) (saved : Store)
    (sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) =
      encodeCellBits (.rational value)) :
    ∃ (ready : State) (path : Path (program kind target source) (before contents saved) ready),
      ready.l = some (control 3) ∧ ready.var = fieldStore value ∧
      ready.stk 0 = [] ∧ ready.stk 24 = [] ∧
      ready.stk 25 = encodeCellBits (.natural value.num.natAbs) ∧
      ready.stk 26 = encodeCellBits (.natural value.den) ∧
      (∀ reg, ready.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg) =
        contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg)) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 →
        ready.stk other = contents other) ∧
      path.states.length ≤ 128 * (RatMarshal.globalSize contents + 1) := by
  let a := Function.update contents 0 []
  let b := prefixContents contents
  let part0 := Path.single (reset_step kind target source contents saved)
  obtain ⟨part1, size1⟩ := clear_call kind target source 0 contents clearedStore
  obtain ⟨part2, size2⟩ := clear_call kind target source 1 a clearedStore
  have currentSource : b (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) =
      encodeCellBits (.rational value) := (prefix_register contents source).trans sourceCell
  obtain ⟨ready, part3, position, vars, right, left, num, den, registers, frame, time⟩ :=
    reader_call kind target source value b (none, false) (none, ()) currentSource
      (by simp [b, prefixContents]) (by simp [b, prefixContents])
  let joined := ((part0.append part1).append part2).append part3
  have total : joined.states.length ≤ 2 + part1.states.length + part2.states.length + part3.states.length := by
    have first := part0.append_length part1
    have second := (part0.append part1).append_length part2
    have third := ((part0.append part1).append part2).append_length part3
    dsimp only [part0, Path.single] at first second third
    simp only [List.length_cons, List.length_nil] at first second third
    dsimp only [joined, part0, Path.single]
    omega
  have size0bound := RatMarshal.initial_le_globalSize contents 0
  have size24bound := RatMarshal.initial_le_globalSize contents 24
  have srcBound := RatMarshal.initial_le_globalSize contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source)
  have numBound := RatMarshal.initial_le_globalSize contents 25
  have denBound := RatMarshal.initial_le_globalSize contents 26
  have inputBound : RatMarshal.inputSize source 0 1 b ≤ 3 * RatMarshal.globalSize contents := by
    change (b (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source)).length + (b 25).length + (b 26).length ≤ _
    dsimp only [b]
    rw [prefix_register, prefix_25, prefix_26]
    omega
  have coarse : joined.states.length ≤ 128 * (RatMarshal.globalSize contents + 1) := by
    change part1.states.length = (contents 0).length + 2 at size1
    change part2.states.length = (a 24).length + 2 at size2
    have same24 : a 24 = contents 24 := by simp [a]
    rw [same24] at size2
    rw [size1, size2] at total
    omega
  refine ⟨ready, joined, position, vars, right, left, num, den, ?_, ?_, coarse⟩
  · intro reg
    exact (registers reg).trans (prefix_register contents reg)
  · intro other not0 not24 not25 not26
    rw [frame other not0 not24 not25 not26]
    dsimp only [b, prefixContents]
    rw [Function.update_of_ne not24, Function.update_of_ne not0]

end PDROC.BitVM.Codec.FieldOps
