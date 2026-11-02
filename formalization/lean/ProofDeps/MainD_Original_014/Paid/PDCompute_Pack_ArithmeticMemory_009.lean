module
public import Paid.PDCompute_Pack_PointerArithmetic_006
public import Paid.PDLower_CalibrationCompute_ReadOnly_051

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute readOnly linearReadOnly_heap)

theorem pointerArithmetic_readOnly : pointerArithmeticCode.all readOnly=true := rfl

/-- All actual successful prefixes, not just the terminal state. The
general physical-memory theorem is reused from the frozen ReadOnly001. -/
theorem pointerArithmetic_prefix_memory (input : List Cell) (before after : State) (base count : ℕ)
    (execute : linearExecute input (pointerArithmeticCode.take count) before=some after) :
    HeaderMemory before after base := by
  have safe : (pointerArithmeticCode.take count).all readOnly=true := by
    apply List.all_eq_true.mpr
    intro instruction member
    exact (List.all_eq_true.mp pointerArithmetic_readOnly) instruction (List.mem_of_mem_take member)
  have unchanged:=linearReadOnly_heap input (pointerArithmeticCode.take count) before after safe execute
  exact HeaderMemory.of_unchanged base unchanged.1 unchanged.2.1 unchanged.2.2

theorem pointerArithmetic_header (before : State) (base n k : ℕ) (values : ℕ → Cell)
    (header : Header before base values) : Header (pointerArithmeticResult before base n k) base values := by
  apply header.frame
  · intro slot _
    rfl
  · exact Finset.Subset.refl _

end PDCompute.Pack
