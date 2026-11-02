module

public import Paid.PDCompute_SolverBaseRowStep_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem baseRow_body_fetch (program : Program) (origin : ℕ) (hcode : FetchesCode program origin (baseRowCode origin))
    (before : State) (hpc : before.pc=origin+2) : FetchesCode program before.pc baseRowWrites := by
  intro offset hoff
  have ho : offset < 15 := by simpa only [baseRowWrites_length] using hoff
  have h := hcode (offset+2) (by rw [baseRowCode_length]; omega)
  have he : before.pc+offset=origin+(offset+2) := by omega
  rw [he]
  have hf : (baseRowCode origin)[offset+2]?=baseRowWrites[offset]? := by
    change (baseRowBody (origin+1))[offset]?=baseRowWrites[offset]?
    rw [baseRowBody_split,List.getElem?_append_left hoff]
  exact h.trans hf

/-- A real fetched solver loop-body segment: fifteen actual ordinary
instructions followed by the actual absolute jump to its test. -/
theorem baseRowBody_trace (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (baseRowCode origin)) (before : State) (pointer count : ℕ)
    (hpc : before.pc=origin+2) (haddress : before.register .address=.natural pointer)
    (hcount : before.register .index=.natural count) (hone : before.register .flag=.natural 1) :
    ∃ trace : List State,
      trace.head?=some before ∧
      trace.getLast?=some {baseRowWritesResult before pointer count with pc:=origin+1} ∧
      trace.IsChain (fun first later => step program input first=some later) ∧ time program trace ≤ 255 := by
  have hr := baseRowWrites_execute input before pointer count haddress hcount hone
  obtain ⟨trace,hh,hl,hchain,htime,_⟩ := linearExecute_trace_time program input baseRowWrites
    baseRowWrites_straight before _ (baseRow_body_fetch program origin hcode before hpc) hr
  have hjump : program[(baseRowWritesResult before pointer count).pc]?=some (.jump (origin+1)) := by
    have hh : (baseRowCode origin)[17]?=some (.jump (origin+1)) := rfl
    have h := (hcode 17 (by rw [baseRowCode_length]; omega)).trans hh
    change program[before.pc+15]?=some (.jump (origin+1))
    have he : before.pc+15=origin+17 := by omega
    rw [he]
    exact h
  have hs : step program input (baseRowWritesResult before pointer count)=
      some {baseRowWritesResult before pointer count with pc:=origin+1} := by
    simp [step,hjump,Instruction.execute]
  have hc := chain_append_control program input trace _ _ hchain hl hs
  refine ⟨trace++[{baseRowWritesResult before pointer count with pc:=origin+1}],?_,?_,hc.1,?_⟩
  · have hn : trace ≠ [] := by intro he; simp only [he,List.head?_nil,reduceCtorEq] at hh
    simpa only [List.head?_append_of_ne_nil trace hn] using hh
  · simp
  · have hbound : time program trace ≤ 240 := by simpa only [baseRowWrites_length] using htime
    omega

end PDCompute.Solver
