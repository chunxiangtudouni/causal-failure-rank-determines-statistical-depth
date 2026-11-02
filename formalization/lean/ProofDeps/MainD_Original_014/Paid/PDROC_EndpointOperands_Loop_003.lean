module

public import Paid.PDROC_EndpointOperands_Loop_001
public import Paid.PDROC_CalibrationRow_OperandPrefix_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver PDMenu.ComputeFrame RootD27.Bits
open PDLower.CalibrationCompute (linearExecute)
open PDROC.CalibrationRow.Operand

/- Draft only; no compile/cache before the exact parent receipt. -/

theorem ControlledPrefix.safe (program : Program) (input : List Cell)
    (code : List Instruction) (before state : State) (target budget : ℕ)
    (literal : PrefixSafe input code before budget) (targetBits : natBits target ≤ budget)
    (actual : ControlledPrefix program input code before target state) : SafeBits state budget := by
  rcases actual with ⟨count, _bound, executed⟩ | ⟨middle, executed, _control, same⟩
  · exact literal count state executed
  · subst state
    exact (literal.final executed).withPC target targetBits

theorem ControlledPrefix.memory (program : Program) (input : List Cell)
    (code : List Instruction) (before state : State) (target : ℕ) (region : Finset ℕ)
    (literal : ∀ count ≤ code.length, ∀ after,
      linearExecute input (code.take count) before = some after → RegionMemory before after region)
    (actual : ControlledPrefix program input code before target state) : RegionMemory before state region := by
  rcases actual with ⟨count, bound, executed⟩ | ⟨middle, executed, _control, same⟩
  · exact literal count bound state executed
  · subst state
    exact literal code.length (Nat.le_refl _) middle (by simpa only [List.take_length] using executed)

/-- Select one original straight-block trace exactly once, then append
its one genuine fetched control step. The SAME witness exposes every
actual literal prefix and control endpoint for later pointwise lifting. -/
theorem controlledPrefix_trace (program : Program) (input : List Cell)
    (code : List Instruction) (straight : StraightCode code) (before middle : State) (target : ℕ)
    (fetched : FetchesCode program before.pc code)
    (executed : linearExecute input code before = some middle)
    (control : step program input middle = some {middle with pc := target}) :
    ∃ trace : List State,
      trace.head? = some before ∧ trace.getLast? = some {middle with pc := target} ∧
      trace.IsChain (fun first later => step program input first = some later) ∧
      time program trace ≤ 15 * (code.length + 1) + 15 ∧
      ∀ state ∈ trace, ControlledPrefix program input code before target state := by
  obtain ⟨literal, head, last, chain, cost, prefixes⟩ :=
    linearExecute_trace_time program input code straight before middle fetched executed
  have joined := chain_append_control program input literal middle {middle with pc := target} chain last control
  have nonempty : literal ≠ [] := by
    intro empty
    simp only [empty, List.head?_nil, reduceCtorEq] at head
  refine ⟨literal ++ [{middle with pc := target}], ?_, by simp, joined.1,
    joined.2.trans (Nat.add_le_add_right cost 15), ?_⟩
  · simpa only [List.head?_append_of_ne_nil literal nonempty] using head
  · intro state member
    rcases List.mem_append.mp member with earlier | terminal
    · have split := List.dropLast_append_getLast? middle (by rw [last]; simp)
      rw [←split] at earlier
      rcases List.mem_append.mp earlier with proper | final
      · obtain ⟨count, bound, actual⟩ := prefixes state proper
        exact Or.inl ⟨count, bound.le, actual⟩
      · have same : state = middle := List.mem_singleton.mp final
        subst state
        exact Or.inl ⟨code.length, Nat.le_refl _, by simpa only [List.take_length] using executed⟩
    · have same : state = {middle with pc := target} := List.mem_singleton.mp terminal
      subst state
      exact Or.inr ⟨middle, executed, control, rfl⟩

end PDROC.EndpointOperands.Loop
