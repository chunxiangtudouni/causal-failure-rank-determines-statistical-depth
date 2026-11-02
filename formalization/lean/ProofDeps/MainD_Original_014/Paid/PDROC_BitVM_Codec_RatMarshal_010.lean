module

public import Paid.PDROC_BitVM_Codec_RatMarshal_009
public import Paid.PDROC_BitVM_Common_Occupancy_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.RatMarshal

open Turing PaperProofs.Paid.Computation

/-- Existing physical data, including every unchanged old register. This
is only a proof bound, never input or a prepared workspace to the machine. -/
def globalSize (contents : Stack → List Bool) : ℕ :=
  ∑ role : Stack, (contents role).length

def spaceBound (source : Register) (num den : Fin 7) (different : num ≠ den)
    (contents : Stack → List Bool) : ℕ :=
  globalSize contents + PDROC.BitVM.Common.sourcePushCap (program source num den different) Finset.univ *
    (32 * (inputSize source num den contents + 1))

theorem initial_le_globalSize (contents : Stack → List Bool) (role : Stack) :
    (contents role).length ≤ globalSize contents := by
  unfold globalSize
  exact Finset.single_le_sum (s := Finset.univ) (f := fun index : Stack => (contents index).length)
    (a := role) (fun _ _ => Nat.zero_le _) (Finset.mem_univ role)

theorem register_not_left (reg : Register) :
    PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg ≠ 24 := by
  intro same
  have value := congrArg Fin.val same
  have bounds := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_bounds reg
  change (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg).val = 24 at value
  omega

theorem register_not_temp (reg : Register) (temp : Fin 7) :
    PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg ≠ tempSlot temp := by
  intro same
  have value := congrArg Fin.val same
  have regBounds := PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_bounds reg
  have tempBounds := tempSlot_bounds temp
  omega

/-- The exported actual reader picks build's trace ONCE, then adds occupied
stack bounds to that very witness. Source and all seven original registers
are preserved even when two logical operand registers alias. The two
destination temporaries must be distinct, and their old contents may be
arbitrary. All other temporary/ROM/heap/output/tick roles are framed. -/
theorem runs (source : Register) (num den : Fin 7) (different : num ≠ den)
    (value : ℚ) (contents : Stack → List Bool) (store : Store)
    (sourceCell : contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot source) =
      encodeCellBits (.rational value))
    (rightEmpty : contents 0 = []) (leftEmpty : contents 24 = []) :
    ∃ (run : List State) (after : State),
      run.head? = some (before contents store) ∧
      run.IsChain (fun a b => TM2.step (program source num den different) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program source num den different) after = none ∧
      after.l = none ∧ after.var = (none, decide (value < 0)) ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧
      after.stk (tempSlot num) = encodeCellBits (.natural value.num.natAbs) ∧
      after.stk (tempSlot den) = encodeCellBits (.natural value.den) ∧
      (∀ other, other ≠ 0 → other ≠ 24 → other ≠ tempSlot num → other ≠ tempSlot den →
        after.stk other = contents other) ∧
      (∀ reg, after.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg) =
        contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg)) ∧
      run.length ≤ 32 * (inputSize source num den contents + 1) ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ spaceBound source num den different contents := by
  obtain ⟨after, path, halted, sign, right, left, numerator, denominator, frame, time⟩ :=
    build source num den different value contents store sourceCell rightEmpty leftEmpty
  have stopped : TM2.step (program source num den different) after = none := by
    rcases after with ⟨label, finiteStore, data⟩
    change label = none at halted
    subst label
    rfl
  refine ⟨path.states, after, path.first, path.actual, path.last, stopped, halted, sign,
    right, left, numerator, denominator, frame, ?_, time, ?_⟩
  · intro reg
    exact frame _ (source_not_right reg) (register_not_left reg)
      (register_not_temp reg num) (register_not_temp reg den)
  · cases states : path.states with
    | nil =>
      have impossible := path.first
      simp only [states, List.head?_nil, reduceCtorEq] at impossible
    | cons start rest =>
      have first : start = before contents store := by
        have first := path.first
        rw [states] at first
        exact Option.some.inj first
      have initial : ∀ role, (start.stk role).length ≤ globalSize contents := by
        rw [first]
        exact initial_le_globalSize contents
      have bounded := PDROC.BitVM.Common.source_path_occupancy
        (program source num den different) Finset.univ (supports source num den different)
        start rest (globalSize contents)
        (by rw [first]; exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _))
        initial (by rw [← states]; exact path.actual)
      have length : rest.length ≤ 32 * (inputSize source num den contents + 1) := by
        rw [states] at time
        simp only [List.length_cons] at time
        omega
      intro state member role
      exact ((bounded state member).2 role).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)

end PDROC.BitVM.Codec.RatMarshal
