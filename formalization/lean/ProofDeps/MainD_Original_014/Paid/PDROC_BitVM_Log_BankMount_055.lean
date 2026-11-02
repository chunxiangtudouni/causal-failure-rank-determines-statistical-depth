module

public import Paid.PDROC_BitVM_Log_BankMount_054

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.Log.BankMount

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! Caller-relative time bound for the SAME completed mount witness. Actual
old bank/work bytes are retained in preCap; there is no P-only scratch bound. -/

theorem fieldCount_bits (core : Bool) : natBits (fieldCount core) ≤ 4 := by cases core <;> decide

theorem mountBudget_le (core : Bool) (cells : List Cell) (contents : Stack → List Bool)
    (size : cells.length = fieldCount core) :
    mountBudget core cells contents ≤ 1000 * (preCap contents + (encodeBits cells).length + 1) := by
  have countBound : cells.length ≤ 13 := size.symm ▸ fieldCount_le core
  have bitsBound := fieldCount_bits core
  have headerBound : (encodeNatBits (fieldCount core)).length ≤ 9 := by
    rw [Log.nat_word_length]
    omega
  have inputBound : (cells.flatMap encodeCellBits).length ≤ (encodeBits cells).length := by
    simp only [encodeBits, List.length_append, List.length_cons, List.length_nil]
    omega
  unfold mountBudget readyBudget clearBudget
  omega

/-- One original encoded input is physically read into its6/13 slots and
really cleaned up. This is not a full prepare/core or whole Bool VM theorem. -/
theorem runs_poly (core : Bool) (cells : List Cell) (suffix : List Bool) (before : State)
    (position : before.l = some startLabel) (size : cells.length = fieldCount core)
    (input : before.stk 0 = encodeBits cells ++ suffix) :
    ∃ (run : List State) (after : State),
      run.head? = some before ∧ run.IsChain (fun a b => TM2.step (program core) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (program core) after = none ∧ after.l = none ∧
      Query.equality after.var.2.1 = true ∧ Mounted before.stk cells suffix after.stk ∧
      run.length ≤ 1000 * (preCap before.stk + (encodeBits cells).length + 1) := by
  obtain ⟨run, after, head, chain, last, halt, done, flag, mounted, length⟩ := runs core cells suffix before position size input
  exact ⟨run, after, head, chain, last, halt, done, flag, mounted, length.trans (mountBudget_le core cells before.stk size)⟩

end PDROC.BitVM.Log.BankMount
