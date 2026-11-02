module

public import Paid.PDROC_BitVM_Codec_FieldOps_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.FieldOps

open Turing PaperProofs.Paid.Computation

def logicalAfter (logical : PaperProofs.Paid.Computation.State) (target : Register) (result : ℕ) :
    PaperProofs.Paid.Computation.State :=
  ({ logical with pc := logical.pc + 1 }).set target (.natural result)

theorem execute_field (input : List Cell) (kind : Kind) (target source : Register)
    (logical : PaperProofs.Paid.Computation.State) (value : ℚ)
    (sourceValue : logical.register source = .rational value) :
    (kind.instruction target source).execute input logical =
      some (logicalAfter logical target (kind.value value)) := by
  cases kind <;> simp [Kind.instruction, Kind.value, Instruction.execute, sourceValue,
    Cell.rat?, logicalAfter]

def spaceBound (kind : Kind) (target source : Register) (contents : Stack → List Bool) : ℕ :=
  RatMarshal.globalSize contents + PDROC.BitVM.Common.sourcePushCap (program kind target source) Finset.univ *
    (512 * (RatMarshal.globalSize contents + 1))

/-- Original three field opcodes, not a new ISA. This calls build ONCE;
the exact same actual trace carries the source-RAM success equation, all
register updates/frames, real workspace cleanup, time and occupied space.
Arbitrary old work bytes are paid for by actual entry clears. -/
theorem instruction_runs (input : List Cell) (kind : Kind) (target source : Register)
    (logical : PaperProofs.Paid.Computation.State) (value : ℚ)
    (contents : Stack → List Bool) (saved : Store)
    (represented : ∀ reg, contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg) =
      encodeCellBits (logical.register reg))
    (sourceValue : logical.register source = .rational value) :
    ∃ (run : List State) (after : State),
      (kind.instruction target source).execute input logical =
        some (logicalAfter logical target (kind.value value)) ∧
      run.head? = some (before contents saved) ∧
      run.IsChain (fun a b => TM2.step (program kind target source) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program kind target source) after = none ∧
      after.var = clearedStore ∧
      PDROC.BitVM.Kernel.RegisterGlobal.RegistersRepresent (logicalAfter logical target (kind.value value)) after ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧ after.stk 25 = [] ∧ after.stk 26 = [] ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ 25 → other ≠ 26 →
        other ≠ PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target → after.stk other = contents other) ∧
      run.length ≤ 512 * (RatMarshal.globalSize contents + 1) ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ spaceBound kind target source contents := by
  have sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) =
      encodeCellBits (.rational value) := by rw [represented source, sourceValue]
  obtain ⟨after, path, halted, store, targetWord, work0, work24, work25, work26, frame, time⟩ :=
    build kind target source value contents saved sourceCell
  have stopped : TM2.step (program kind target source) after = none := by
    rcases after with ⟨label, finiteStore, data⟩
    change label = none at halted
    subst label
    rfl
  refine ⟨path.states, after, execute_field input kind target source logical value sourceValue,
    path.first, path.actual, path.last, stopped, store, ?_, work0, work24, work25, work26, frame, time, ?_⟩
  · intro reg
    by_cases selected : reg = target
    · subst reg
      simpa only [logicalAfter, PaperProofs.Paid.Computation.State.set, Function.update_self] using targetWord
    · have unchanged : (logicalAfter logical target (kind.value value)).register reg = logical.register reg :=
        Function.update_of_ne selected _ _
      rw [unchanged]
      exact (frame _ (RatMarshal.source_not_right reg) (RatMarshal.register_not_left reg)
        (RatMarshal.register_not_temp reg 0) (RatMarshal.register_not_temp reg 1)
        (fun same => selected (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_injective same))).trans (represented reg)
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
      have bounded := PDROC.BitVM.Common.source_path_occupancy (program kind target source)
        Finset.univ (supports kind target source) start rest (RatMarshal.globalSize contents)
        (by rw [first]; exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _))
        initial (by rw [← states]; exact path.actual)
      have length : rest.length ≤ 512 * (RatMarshal.globalSize contents + 1) := by
        rw [states] at time
        simp only [List.length_cons] at time
        omega
      intro state member role
      exact ((bounded state member).2 role).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)

end PDROC.BitVM.Codec.FieldOps
