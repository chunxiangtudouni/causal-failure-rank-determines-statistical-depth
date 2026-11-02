module

public import Paid.PDROC_BitVM_Codec_RatAssembler_013
public import Paid.PDROC_BitVM_Codec_RatMarshal_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.RatAssembler

open Turing PaperProofs.Paid.Computation

def spaceBound (target : Register) (num den : Fin 7) (contents : Stack → List Bool) : ℕ :=
  RatMarshal.globalSize contents +
    PDROC.BitVM.Common.sourcePushCap (program target num den) Finset.univ *
      (32 * (inputSize target num den contents + 1))

/-- Canonical Cell specialization of the same actual byte assembler path.
The actual arithmetic caller supplies its already-produced Nat Cells and
finite sign, with these semantic representation proofs. There is no Rat
decode, normalization or answer selection inside the machine. -/
theorem runs (target : Register) (num den : Fin 7) (value : ℚ)
    (contents : Stack → List Bool) (saved : Option Bool) (sign : Bool)
    (signValue : sign = decide (value < 0))
    (numerator : contents (RatMarshal.tempSlot num) = encodeCellBits (.natural value.num.natAbs))
    (denominator : contents (RatMarshal.tempSlot den) = encodeCellBits (.natural value.den)) :
    ∃ (run : List State) (after : State),
      run.head? = some (before contents saved sign) ∧
      run.IsChain (fun a b => TM2.step (program target num den) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program target num den) after = none ∧
      after.l = none ∧ after.var = (none, sign) ∧
      after.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) = encodeCellBits (.rational value) ∧
      after.stk 24 = [] ∧ after.stk 0 = contents 0 ∧
      (∀ other, other ≠ PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target → other ≠ 24 →
        after.stk other = contents other) ∧
      (∀ temp, after.stk (RatMarshal.tempSlot temp) = contents (RatMarshal.tempSlot temp)) ∧
      (∀ reg, reg ≠ target → after.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg) =
        contents (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot reg)) ∧
      run.length ≤ 32 * (inputSize target num den contents + 1) ∧
      ∀ state ∈ run, ∀ role, (state.stk role).length ≤ spaceBound target num den contents := by
  obtain ⟨after, path, halted, store, targetWord, scratch, frame, time⟩ :=
    build target num den (encodeNatBits value.num.natAbs) (encodeNatBits value.den)
      contents saved sign numerator denominator
  have stopped : TM2.step (program target num den) after = none := by
    rcases after with ⟨label, finiteStore, data⟩
    change label = none at halted
    subst label
    rfl
  have exactCell : after.stk (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot target) =
      encodeCellBits (.rational value) := by
    simpa only [signValue, encodeCellBits, List.cons_append, List.nil_append] using targetWord
  refine ⟨path.states, after, path.first, path.actual, path.last, stopped, halted, store,
    exactCell, scratch, ?_, frame, ?_, ?_, time, ?_⟩
  · exact frame 0 (Ne.symm (RatMarshal.source_not_right target)) (by decide)
  · intro temp
    exact frame _ (temp_not_target temp target) (RatMarshal.temp_not_left temp)
  · intro reg different
    apply frame
    · exact fun same => different (PDROC.BitVM.Kernel.RegisterGlobal.registerSlot_injective same)
    · exact RatMarshal.register_not_left reg
  · cases states : path.states with
    | nil =>
      have impossible := path.first
      simp only [states, List.head?_nil, reduceCtorEq] at impossible
    | cons start rest =>
      have first : start = before contents saved sign := by
        have first := path.first
        rw [states] at first
        exact Option.some.inj first
      have initial : ∀ role, (start.stk role).length ≤ RatMarshal.globalSize contents := by
        rw [first]
        exact RatMarshal.initial_le_globalSize contents
      have bounded := PDROC.BitVM.Common.source_path_occupancy (program target num den)
        Finset.univ (supports target num den) start rest (RatMarshal.globalSize contents)
        (by rw [first]; exact Finset.some_mem_insertNone.mpr (Finset.mem_univ _))
        initial (by rw [← states]; exact path.actual)
      have length : rest.length ≤ 32 * (inputSize target num den contents + 1) := by
        rw [states] at time
        simp only [List.length_cons] at time
        omega
      intro state member role
      exact ((bounded state member).2 role).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_left _ length) _)

end PDROC.BitVM.Codec.RatAssembler
