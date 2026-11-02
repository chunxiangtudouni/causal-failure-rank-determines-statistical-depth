module

public import Paid.PDMenu_ComputeFrame_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

/-- Transport every real adjacent Step of a callee fragment. The final
returned caller state is deliberately excluded from the callee fetch domain. -/
theorem chain_transport (left right : Program) (leftInput rightInput : List Cell) :
    ∀ trace : List State,
      (∀ state ∈ trace.dropLast, left[state.pc]? = right[state.pc]?) →
      (∀ state ∈ trace.dropLast, ∀ instruction, left[state.pc]? = some instruction → NoInputInstruction instruction) →
      trace.IsChain (fun before after => step left leftInput before = some after) →
      trace.IsChain (fun before after => step right rightInput before = some after) := by
  intro trace
  induction trace with
  | nil => intro _ _ _; exact .nil
  | cons before tail ih =>
      intro hf hno hc
      cases tail with
      | nil => exact .singleton before
      | cons after rest =>
          have hp := List.isChain_cons_cons.mp hc
          have hm : before ∈ (before::after::rest).dropLast := by simp
          apply List.isChain_cons_cons.mpr
          refine ⟨?_, ih ?_ ?_ hp.2⟩
          · rw [← step_eq_of_fetch_eq_noInput left right leftInput rightInput before (hf before hm) (hno before hm)]
            exact hp.1
          · intro state hs
            exact hf state (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact Or.inr hs)
          · intro state hs instruction hi
            exact hno state (by simp only [List.dropLast_cons_cons, List.mem_cons]; exact Or.inr hs) instruction hi

theorem primitiveTrace_eq_of_fetch_eq (left right : Program) (trace : List State)
    (hf : ∀ state ∈ trace, left[state.pc]? = right[state.pc]?) :
    primitiveTrace left trace = primitiveTrace right trace := by
  apply List.flatMap_congr
  intro state hs
  rw [hf state hs]

/-- The caller's returned state may fetch its next actual instruction.
That real closing fetch is charged, with a uniform primitive bound of15. -/
theorem time_le_of_dropLast_fetch_eq (left right : Program) (trace : List State)
    (hf : ∀ state ∈ trace.dropLast, left[state.pc]? = right[state.pc]?) :
    time right trace ≤ time left trace+15 := by
  by_cases he : trace=[]
  · subst trace; simp [time, primitiveTrace]
  · have htrace := List.dropLast_append_getLast he
    have hprefix : time left trace.dropLast = time right trace.dropLast :=
      congrArg List.length (primitiveTrace_eq_of_fetch_eq left right trace.dropLast hf)
    calc
      _ = time right (trace.dropLast++[trace.getLast he]) := congrArg (time right) htrace.symm
      _ = time right trace.dropLast+time right [trace.getLast he] := time_append _ _ _
      _ ≤ time left trace.dropLast+15 := by rw [hprefix]; exact Nat.add_le_add_left (time_singleton_le _ _) _
      _ ≤ time left trace+15 := by
        apply Nat.add_le_add_right
        have hfull : time left trace = time left trace.dropLast+time left [trace.getLast he] := by
          calc
            _ = time left (trace.dropLast++[trace.getLast he]) := congrArg (time left) htrace.symm
            _ = _ := time_append _ _ _
        rw [hfull]
        exact Nat.le_add_right _ _

/-- A real heap-only callee with origin-relative code generation embeds
between arbitrary actual caller prefix/suffix programs, keeping every
state and every absolute indirect-return PC unchanged. -/
theorem chain_appendBlock (beforeCode code suffix : Program) (leftInput rightInput : List Cell)
    (trace : List State)
    (hscope : ∀ state ∈ trace.dropLast, beforeCode.size ≤ state.pc ∧ state.pc < beforeCode.size+code.size)
    (hcode : ∀ offset, offset < code.size → ∀ instruction, code[offset]? = some instruction → NoInputInstruction instruction)
    (hc : trace.IsChain (fun before after => step (locatedBlock beforeCode.size code) leftInput before = some after)) :
    trace.IsChain (fun before after => step (beforeCode++code++suffix) rightInput before = some after) ∧
      time (beforeCode++code++suffix) trace ≤ time (locatedBlock beforeCode.size code) trace+15 := by
  have hf : ∀ state ∈ trace.dropLast,
      (locatedBlock beforeCode.size code)[state.pc]? = (beforeCode++code++suffix)[state.pc]? :=
    fun state hs => appendBlock_fetch_located beforeCode code suffix state (hscope state hs).1 (hscope state hs).2
  have hno : ∀ state ∈ trace.dropLast, ∀ instruction,
      (locatedBlock beforeCode.size code)[state.pc]? = some instruction → NoInputInstruction instruction := by
    intro state hs instruction hi
    have hp : state.pc = beforeCode.size+(state.pc-beforeCode.size) := by have h := hscope state hs; omega
    rw [hp, locatedBlock_fetch] at hi
    exact hcode _ (by have h := hscope state hs; omega) instruction hi
  exact ⟨chain_transport _ _ leftInput rightInput trace hf hno hc,
    time_le_of_dropLast_fetch_eq _ _ trace hf⟩

end PDMenu.ComputeFrame
