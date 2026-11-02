module

public import Paid.PDROC_BitVM_Codec_OutputInstruction_001
public import Paid.PDROC_BitVM_Codec_FieldOps_020
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.OutputInstruction

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Codec.FieldOps (Path)

def logicalAfter (logical : PaperProofs.Paid.Computation.State) (source : Register) :
    PaperProofs.Paid.Computation.State :=
  { logical with pc := logical.pc + 1, output := logical.output ++ [logical.register source] }

theorem execute_output (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (source : Register) :
    Instruction.execute input (.output source) logical = some (logicalAfter logical source) := rfl

/-- One actual original output path. Both old work stacks are genuinely
cleared. Complete Cell copy, reverse byte emission and ONE count tick
precede the final true source-buffer cleanup. No host list operation is
used by the machine transition; list append is only the specification. -/
theorem build (logical : PaperProofs.Paid.Computation.State) (source : Register)
    (contents : Stack → List Bool) (saved : Store)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (outputWord : contents 22 = (logical.output.flatMap encodeCellBits).reverse)
    (outputTicks : contents 23 = List.replicate logical.output.length true) :
    ∃ after : State, ∃ path : Path (program source) (before contents saved) after,
      after.l = none ∧ after.var = clearedStore ∧ after.stk 0 = [] ∧ after.stk 24 = [] ∧
      after.stk 22 = ((logicalAfter logical source).output.flatMap encodeCellBits).reverse ∧
      after.stk 23 = List.replicate (logicalAfter logical source).output.length true ∧
      (∀ other, other ≠ 0 → other ≠ 22 → other ≠ 24 → other ≠ 23 → after.stk other = contents other) ∧
      path.states.length ≤ 32 * (RatMarshal.globalSize contents + 1) := by
  let word := encodeCellBits (logical.register source)
  let old0 := Function.update contents 0 []
  let entry := FieldOps.prefixContents contents
  let part0 := Path.single (reset_step source contents saved)
  obtain ⟨part1, size1⟩ := clear_call source 0 contents none
  obtain ⟨part2, size2⟩ := clear_call source 1 old0 none
  have entryRep : ∀ reg, entry (registerSlot reg) = encodeCellBits (logical.register reg) :=
    fun reg => (FieldOps.prefix_register contents reg).trans (represented reg)
  obtain ⟨readEnd, readPath, readPos, readStore, read0, read24, readFrame, readTime⟩ :=
    reader_call source logical entry entryRep (by simp [entry, FieldOps.prefixContents])
      (by simp [entry, FieldOps.prefixContents])
  have readEq := state_at_label readEnd (emitLabels 0) readPos
  rw [readStore] at readEq
  let part3 := readPath.castLast readEq
  obtain ⟨emitted, emitPath, emitPos, emitStore, emit0, emit24, emit22, emit23, emitFrame, emitTime⟩ :=
    emit_call source word readEnd.stk read0 read24
  have emitEq := state_at_label emitted (control 3) emitPos
  rw [emitStore] at emitEq
  let part4 := emitPath.castLast emitEq
  obtain ⟨part5, size5⟩ := clear_call source 2 emitted.stk none
  let finalContents := Function.update emitted.stk 0 []
  let part6 := Path.single (finish_step source finalContents clearedStore)
  let joined := (((((part0.append part1).append part2).append part3).append part4).append part5).append part6
  have current22 : readEnd.stk 22 = contents 22 := by
    rw [readFrame 22 (by decide) (by decide)]
    simp [entry, FieldOps.prefixContents]
  have current23 : readEnd.stk 23 = contents 23 := by
    rw [readFrame 23 (by decide) (by decide)]
    simp [entry, FieldOps.prefixContents]
  have finalOutput : finalContents 22 = ((logicalAfter logical source).output.flatMap encodeCellBits).reverse := by
    dsimp only [finalContents]
    rw [Function.update_of_ne (by decide : (22 : Stack) ≠ 0), emit22, current22, outputWord]
    simp only [logicalAfter, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.reverse_append, word]
  have finalTicks : finalContents 23 = List.replicate (logicalAfter logical source).output.length true := by
    dsimp only [finalContents]
    rw [Function.update_of_ne (by decide : (23 : Stack) ≠ 0), emit23, current23, outputTicks]
    simp [logicalAfter, List.replicate_succ]
  have total : joined.states.length ≤ 2 + part1.states.length + part2.states.length + part3.states.length +
      part4.states.length + part5.states.length + 2 := by
    have h1 := part0.append_length part1
    have h2 := (part0.append part1).append_length part2
    have h3 := ((part0.append part1).append part2).append_length part3
    have h4 := (((part0.append part1).append part2).append part3).append_length part4
    have h5 := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    have h6 := (((((part0.append part1).append part2).append part3).append part4).append part5).append_length part6
    dsimp only [part0, part6, Path.single] at h1 h2 h3 h4 h5 h6
    simp only [List.length_cons, List.length_nil] at h1 h2 h3 h4 h5 h6
    dsimp only [joined, part0, part6, Path.single]
    omega
  have time : joined.states.length ≤ 32 * (RatMarshal.globalSize contents + 1) := by
    change part1.states.length = (contents 0).length + 2 at size1
    change part2.states.length = (old0 24).length + 2 at size2
    have same24 : old0 24 = contents 24 := by simp [old0]
    rw [same24] at size2
    change part3.states.length = 2 * word.length + 3 at readTime
    change part4.states.length = 2 * word.length + 4 at emitTime
    change part5.states.length = (emitted.stk 0).length + 2 at size5
    rw [emit0] at size5
    rw [size1, size2, readTime, emitTime, size5] at total
    have bound0 := RatMarshal.initial_le_globalSize contents 0
    have bound24 := RatMarshal.initial_le_globalSize contents 24
    have width := RatMarshal.initial_le_globalSize contents (registerSlot source)
    rw [represented source] at width
    change word.length ≤ RatMarshal.globalSize contents at width
    omega
  refine ⟨(⟨none, clearedStore, finalContents⟩ : State), joined, rfl, rfl, ?_, ?_, finalOutput, finalTicks, ?_, time⟩
  · change finalContents (0 : Stack) = []
    exact Function.update_self (0 : Stack) ([] : List Bool) emitted.stk
  · change finalContents 24 = []
    dsimp only [finalContents]
    rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 0)]
    exact emit24
  · intro other not0 not22 not24 not23
    change finalContents other = contents other
    dsimp only [finalContents]
    rw [Function.update_of_ne not0, emitFrame other not0 not22 not24 not23, readFrame other not0 not24]
    dsimp only [entry, FieldOps.prefixContents]
    rw [Function.update_of_ne not24, Function.update_of_ne not0]

def spaceBound (source : Register) (contents : Stack → List Bool) : ℕ :=
  RatMarshal.globalSize contents + PDROC.BitVM.Common.sourcePushCap (program source) Finset.univ *
    (32 * (RatMarshal.globalSize contents + 1))

/-- Original output success, complete original-register frame, exact
reverse-byte/tick event invariant and ALL physical-space states refer to
the SAME selected genuine output path. No work-emptiness input condition. -/
theorem instruction_runs (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (source : Register)
    (contents : Stack → List Bool) (saved : Store)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (outputWord : contents 22 = (logical.output.flatMap encodeCellBits).reverse)
    (outputTicks : contents 23 = List.replicate logical.output.length true) :
    ∃ (run : List State) (after : State),
      Instruction.execute input (.output source) logical = some (logicalAfter logical source) ∧
      run.head? = some (before contents saved) ∧ run.IsChain (fun a b => TM2.step (program source) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program source) after = none ∧ after.var = clearedStore ∧
      RegistersRepresent (logicalAfter logical source) after ∧ after.stk 0 = [] ∧ after.stk 24 = [] ∧
      after.stk 22 = ((logicalAfter logical source).output.flatMap encodeCellBits).reverse ∧
      after.stk 23 = List.replicate (logicalAfter logical source).output.length true ∧
      (∀ other, other ≠ 0 → other ≠ 22 → other ≠ 24 → other ≠ 23 → after.stk other = contents other) ∧
      run.length ≤ 32 * (RatMarshal.globalSize contents + 1) ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ spaceBound source contents := by
  obtain ⟨after, path, halted, store, work0, work24, output, ticks, frame, time⟩ :=
    build logical source contents saved represented outputWord outputTicks
  have stopped : TM2.step (program source) after = none := by
    rcases after with ⟨label, finiteStore, data⟩
    change label = none at halted
    subst label
    rfl
  refine ⟨path.states, after, execute_output input logical source, path.first, path.actual, path.last, stopped,
    store, ?_, work0, work24, output, ticks, frame, time, ?_⟩
  · intro reg
    exact (frame _ (register_outside reg 0) (register_outside reg 1)
      (register_outside reg 2) (register_outside reg 3)).trans (represented reg)
  · cases states : path.states with
    | nil =>
      have impossible := path.first
      simp only [states, List.head?_nil, reduceCtorEq] at impossible
    | cons start rest =>
      have first : start = before contents saved := by
        have first := path.first
        rw [states] at first
        exact Option.some.inj first
      have initial : ∀ role, (start.stk role).length ≤ RatMarshal.globalSize contents := by
        rw [first]
        exact RatMarshal.initial_le_globalSize contents
      have bounded := PDROC.BitVM.Common.source_path_occupancy (program source) Finset.univ (supports source)
        start rest (RatMarshal.globalSize contents)
        (by rw [first]; exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _)) initial
        (by rw [← states]; exact path.actual)
      have length : rest.length ≤ 32 * (RatMarshal.globalSize contents + 1) := by
        rw [states] at time
        simp only [List.length_cons] at time
        omega
      intro state member role
      exact ((bounded state member).2 role).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)

end PDROC.BitVM.Codec.OutputInstruction
