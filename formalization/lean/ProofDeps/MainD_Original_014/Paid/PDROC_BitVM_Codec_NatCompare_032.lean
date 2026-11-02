module

public import Paid.PDROC_BitVM_Codec_NatCompare_031

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Codec.NatCompare

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PDROC.BitVM.Codec.FieldOps (Path)

def budget (left right : Register) (contents : Stack → List Bool) (a b : ℕ) : ℕ :=
  readBudget left right contents a b + 64 * (RatMarshal.globalSize contents + 4)

def logicalAfter (comparison : Comparison) (logical : PaperProofs.Paid.Computation.State)
    (target : Register) (a b : ℕ) : PaperProofs.Paid.Computation.State :=
  ({ logical with pc := logical.pc + 1 }).set target (.natural (if comparison.nat a b then 1 else 0))

theorem execute_compare (input : List Cell) (comparison : Comparison) (target left right : Register)
    (logical : PaperProofs.Paid.Computation.State) (a b : ℕ)
    (leftNat : logical.register left = .natural a) (rightNat : logical.register right = .natural b) :
    Instruction.execute input (.natCompare comparison target left right) logical =
      some (logicalAfter comparison logical target a b) := by
  simp [Instruction.execute, leftNat, rightNat, Cell.nat?, logicalAfter]

/-- One complete actual original comparison path, including old-work
cleanup, two source reads, both native LE calls, Bool inspections, true
canonical writeback and true temporary cleanup. No alias restriction. -/
theorem build (comparison : Comparison) (target left right : Register)
    (logical : PaperProofs.Paid.Computation.State) (a b : ℕ)
    (contents : Stack → List Bool) (saved : Store)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (leftNat : logical.register left = .natural a) (rightNat : logical.register right = .natural b) :
    ∃ after : State, ∃ path : Path (program comparison target left right) (before contents saved) after,
      after.l = none ∧ after.var = clearedStore ∧
      after.stk (registerSlot target) = encodeCellBits (.natural (if comparison.nat a b then 1 else 0)) ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧ after.stk 25 = [] ∧ after.stk 26 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 →
        other ≠ registerSlot target → after.stk other = contents other) ∧
      path.states.length ≤ budget left right contents a b := by
  obtain ⟨ready, readPath, readPos, flag, rightEmpty, leftEmpty, cell25, cell26, registers, readFrame, readTime⟩ :=
    read_both comparison target left right logical a b contents saved represented leftNat rightNat
  have readyEq : ready = (⟨some (control 6), ready.var, ready.stk⟩ : State) :=
    state_at_label ready (control 6) readPos
  let part0 := readPath.castLast readyEq
  let word := encodeNatBits (if comparison.nat a b then 1 else 0)
  let next := Function.update ready.stk 0 word
  have pushEdge := push_step comparison target left right ready.stk ready.var
  rw [flag, rightEmpty, List.append_nil] at pushEdge
  let part1 := Path.single pushEdge
  have representation : ListBlank.mk (next 0) = ListBlank.mk
      (PaperProofs.Common.Native.RationalControllerComputation.encodeNat (if comparison.nat a b then 1 else 0)) := by
    simp only [next, word, Function.update_self, PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral]
  obtain ⟨written, writePath, writePos, work0, work24, targetWord, writeFrame, writeTime⟩ :=
    writer_call comparison target left right (if comparison.nat a b then 1 else 0) next ready.var representation
  have writtenEq : written = (⟨some (control 7), written.var, written.stk⟩ : State) :=
    state_at_label written (control 7) writePos
  let part2 := writePath.castLast writtenEq
  obtain ⟨part3, size3⟩ := clear_call comparison target left right 2 written.stk written.var
  let e := Function.update written.stk 25 []
  let store3 : Store := ((none, written.var.1.2), written.var.2)
  obtain ⟨part4, size4⟩ := clear_call comparison target left right 3 e store3
  let f := Function.update e 26 []
  let part5 := Path.single (finish_step comparison target left right f store3)
  let joined := ((((part0.append part1).append part2).append part3).append part4).append part5
  have not0 := RatMarshal.source_not_right target
  have not24 := RatMarshal.register_not_left target
  have not25 : registerSlot target ≠ (25 : Stack) := RatMarshal.register_not_temp target 0
  have not26 : registerSlot target ≠ (26 : Stack) := RatMarshal.register_not_temp target 1
  have nextTarget : next (registerSlot target) = contents (registerSlot target) := by
    dsimp only [next]
    rw [Function.update_of_ne not0, registers]
  have next24 : next 24 = [] := by simp only [next, Function.update_of_ne (by decide : (24 : Stack) ≠ 0), leftEmpty]
  have next0 : next 0 = word := Function.update_self _ _ _
  have wordLength : word.length = 3 := by
    dsimp only [word]
    rw [FieldOps.bool_word]
    rfl
  have writerBound : part2.states.length ≤ 32 * (RatMarshal.globalSize contents + 4) := by
    change part2.states.length ≤ 32 * ((next 0).length + (next 24).length + (next (registerSlot target)).length + 1) at writeTime
    rw [nextTarget, next24, next0, wordLength] at writeTime
    simp only [List.length_nil] at writeTime
    have initial := RatMarshal.initial_le_globalSize contents (registerSlot target)
    omega
  have old25 : (written.stk 25).length = 4 := by
    rw [writeFrame 25 (by decide) (by decide) (Ne.symm not25)]
    dsimp only [next]
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 0), cell25, bool_cell_length]
  have old26 : (e 26).length = 4 := by
    dsimp only [e]
    rw [Function.update_of_ne (by decide : (26 : Stack) ≠ 25),
      writeFrame 26 (by decide) (by decide) (Ne.symm not26)]
    dsimp only [next]
    rw [Function.update_of_ne (by decide : (26 : Stack) ≠ 0), cell26, bool_cell_length]
  have total : joined.states.length ≤ part0.states.length + 2 + part2.states.length +
      part3.states.length + part4.states.length + 2 := by
    have h1 := part0.append_length part1
    have h2 := (part0.append part1).append_length part2
    have h3 := ((part0.append part1).append part2).append_length part3
    have h4 := (((part0.append part1).append part2).append part3).append_length part4
    have h5 := ((((part0.append part1).append part2).append part3).append part4).append_length part5
    dsimp only [part1, part5, Path.single] at h1 h2 h3 h4 h5
    simp only [List.length_cons, List.length_nil] at h1 h2 h3 h4 h5
    dsimp only [joined, part1, part5, Path.single]
    omega
  have time : joined.states.length ≤ budget left right contents a b := by
    change part3.states.length = (written.stk 25).length + 2 at size3
    change part4.states.length = (e 26).length + 2 at size4
    rw [size3, size4, old25, old26] at total
    change part0.states.length ≤ readBudget left right contents a b at readTime
    unfold budget
    omega
  refine ⟨(⟨none, clearedStore, f⟩ : State), joined, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, time⟩
  · change f (registerSlot target) = _
    dsimp only [f, e]
    rw [Function.update_of_ne not26, Function.update_of_ne not25]
    exact targetWord
  · change f 0 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (0 : Stack) ≠ 26), Function.update_of_ne (by decide : (0 : Stack) ≠ 25)]
    exact work0
  · change f 24 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (24 : Stack) ≠ 26), Function.update_of_ne (by decide : (24 : Stack) ≠ 25)]
    exact work24
  · change f 25 = []
    dsimp only [f, e]
    rw [Function.update_of_ne (by decide : (25 : Stack) ≠ 26), Function.update_self]
  · change f 26 = []
    exact Function.update_self _ _ _
  · intro other no0 no24 no25 no26 noTarget
    change f other = contents other
    dsimp only [f, e]
    rw [Function.update_of_ne no26, Function.update_of_ne no25, writeFrame other no0 no24 noTarget]
    dsimp only [next]
    rw [Function.update_of_ne no0, readFrame other no0 no24 no25 no26]

def spaceBound (comparison : Comparison) (target left right : Register)
    (contents : Stack → List Bool) (a b : ℕ) : ℕ :=
  RatMarshal.globalSize contents + PDROC.BitVM.Common.sourcePushCap (program comparison target left right)
    Finset.univ * budget left right contents a b

/-- Original three Comparison constructors, full original register
semantics and all physical-space states come from exactly one build path.
Only the original typed operands and actual representation are required. -/
theorem instruction_runs (input : List Cell) (comparison : Comparison) (target left right : Register)
    (logical : PaperProofs.Paid.Computation.State) (a b : ℕ)
    (contents : Stack → List Bool) (saved : Store)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (leftNat : logical.register left = .natural a) (rightNat : logical.register right = .natural b) :
    ∃ (run : List State) (after : State),
      Instruction.execute input (.natCompare comparison target left right) logical =
        some (logicalAfter comparison logical target a b) ∧
      run.head? = some (before contents saved) ∧
      run.IsChain (fun x y => TM2.step (program comparison target left right) x = some y) ∧
      run.getLast? = some after ∧ TM2.step (program comparison target left right) after = none ∧
      after.var = clearedStore ∧ RegistersRepresent (logicalAfter comparison logical target a b) after ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧ after.stk 25 = [] ∧ after.stk 26 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 →
        other ≠ registerSlot target → after.stk other = contents other) ∧
      run.length ≤ budget left right contents a b ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ spaceBound comparison target left right contents a b := by
  obtain ⟨after, path, halted, store, targetWord, work0, work24, work25, work26, frame, time⟩ :=
    build comparison target left right logical a b contents saved represented leftNat rightNat
  have stopped : TM2.step (program comparison target left right) after = none := by
    rcases after with ⟨label, finiteStore, data⟩
    change label = none at halted
    subst label
    rfl
  refine ⟨path.states, after, execute_compare input comparison target left right logical a b leftNat rightNat,
    path.first, path.actual, path.last, stopped, store, ?_, work0, work24, work25, work26, frame, time, ?_⟩
  · intro reg
    by_cases selected : reg = target
    · subst reg
      simpa only [logicalAfter, PaperProofs.Paid.Computation.State.set, Function.update_self] using targetWord
    · have unchanged : (logicalAfter comparison logical target a b).register reg = logical.register reg :=
        Function.update_of_ne selected _ _
      rw [unchanged]
      exact (frame _ (RatMarshal.source_not_right reg) (RatMarshal.register_not_left reg)
        (RatMarshal.register_not_temp reg 0) (RatMarshal.register_not_temp reg 1)
        (fun same => selected (registerSlot_injective same))).trans (represented reg)
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
      have bounded := PDROC.BitVM.Common.source_path_occupancy (program comparison target left right)
        Finset.univ (supports comparison target left right) start rest (RatMarshal.globalSize contents)
        (by rw [first]; exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _))
        initial (by rw [← states]; exact path.actual)
      have length : rest.length ≤ budget left right contents a b := by
        rw [states] at time
        simp only [List.length_cons] at time
        omega
      intro state member role
      exact ((bounded state member).2 role).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)

end PDROC.BitVM.Codec.NatCompare
