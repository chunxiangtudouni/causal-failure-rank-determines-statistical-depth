module

public import Paid.PDMenu_ComputeFrame_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)

def FetchesCode (program : Program) (pc : ℕ) (code : List Instruction) : Prop :=
  ∀ offset, offset < code.length → program[pc+offset]?=code[offset]?

/-- Successful literal straight-line execution generates a REAL original
step trace at the actual fetched addresses. Every preterminal trace state
is itself a successfully executed strict prefix of this same instruction
list, so callers can prove all intermediate live/bit bounds. -/
theorem linearExecute_trace (program : Program) (input : List Cell) (code : List Instruction)
    (hstraight : StraightCode code) (before after : State) (hfetch : FetchesCode program before.pc code)
    (hrun : linearExecute input code before=some after) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.length=code.length+1 ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      ∀ state ∈ trace.dropLast, ∃ count < code.length,
        linearExecute input (code.take count) before=some state := by
  induction code generalizing before with
  | nil =>
      simp only [linearExecute,Option.some.injEq] at hrun
      subst after
      refine ⟨[before],rfl,rfl,rfl,.singleton before,?_⟩
      simp
  | cons instruction code ih =>
      obtain ⟨middle,hfirst,hlater⟩ := Option.bind_eq_some_iff.mp hrun
      have hp := execute_pc_succ instruction (hstraight instruction (by simp)) input before middle hfirst
      have hf0 : program[before.pc]?=some instruction := by simpa using hfetch 0 (by simp)
      have hstep : step program input before=some middle := by
        simpa [step,hf0] using hfirst
      have hftail : FetchesCode program middle.pc code := by
        intro offset hoff
        have h := hfetch (offset+1) (by simp only [List.length_cons]; omega)
        have hpc : middle.pc+offset=before.pc+(offset+1) := by omega
        rw [hpc]
        simpa only [List.getElem?_cons_succ] using h
      obtain ⟨tail,hhead,hlast,hlen,hchain,hprefix⟩ :=
        ih (fun i hm => hstraight i (by simp only [List.mem_cons]; exact Or.inr hm)) middle hftail hlater
      cases tail with
      | nil => simp at hhead
      | cons head states =>
          have heq : head=middle := Option.some.inj hhead
          subst head
          refine ⟨before::middle::states,rfl,?_,?_,?_,?_⟩
          · simpa only [List.getLast?_cons_cons] using hlast
          · simp only [List.length_cons] at hlen ⊢
            omega
          · exact List.isChain_cons_cons.mpr ⟨hstep,hchain⟩
          · intro state hm
            simp only [List.dropLast_cons_cons,List.mem_cons] at hm
            rcases hm with he|hm
            · subst state
              exact ⟨0,by simp,rfl⟩
            · obtain ⟨count,hcount,hexec⟩ := hprefix state hm
              refine ⟨count+1,by simp only [List.length_cons]; omega,?_⟩
              simpa only [List.take_succ_cons,linearExecute,hfirst,Option.bind_some] using hexec

theorem linearExecute_trace_time (program : Program) (input : List Cell) (code : List Instruction)
    (hstraight : StraightCode code) (before after : State) (hfetch : FetchesCode program before.pc code)
    (hrun : linearExecute input code before=some after) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 15*(code.length+1) ∧
      ∀ state ∈ trace.dropLast, ∃ count < code.length,
        linearExecute input (code.take count) before=some state := by
  obtain ⟨trace,hh,hl,hlength,hchain,hprefix⟩ := linearExecute_trace program input code hstraight before after hfetch hrun
  refine ⟨trace,hh,hl,hchain,?_,hprefix⟩
  simpa only [hlength] using time_le_length program trace

end PDMenu.ComputeFrame
