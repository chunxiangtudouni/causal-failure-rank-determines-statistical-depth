module

public import Paid.PDCompute_SolverBaseRowTrace_009
public import Paid.PDMenu_ComputeFrame_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def baseRowLoopResult (origin : ℕ) : ℕ → State → ℕ → State
  | 0,before,_ => {before with pc:=origin+18}
  | count+1,before,pointer =>
      let start := {before with pc:=origin+2}
      let returned := {baseRowWritesResult start pointer (count+1) with pc:=origin+1}
      baseRowLoopResult origin count returned (pointer+6)

/-- A genuine counted loop over one fixed eighteen-instruction block.
Every iteration uses an actual branch, fifteen stores/arithmetic steps,
and its actual back jump; no data-dependent program text is generated. -/
theorem baseRowLoop_trace (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (baseRowCode origin)) :
    ∀ (count : ℕ) (before : State) (pointer : ℕ), before.pc=origin+1 →
      before.register .address=.natural pointer → before.register .index=.natural count →
      before.register .flag=.natural 1 →
      ∃ trace : List State, trace.head?=some before ∧
        trace.getLast?=some (baseRowLoopResult origin count before pointer) ∧
        trace.IsChain (fun first later => step program input first=some later) ∧
        time program trace ≤ 300*count+30 := by
  intro count
  induction count with
  | zero =>
      intro before pointer hpc _haddress hcount _hone
      have hf : program[before.pc]?=some (.branchZero .index (origin+18) (origin+2)) := by
        rw [hpc]
        exact hcode 1 (by rw [baseRowCode_length]; omega)
      have hs : step program input before=some {before with pc:=origin+18} := by
        simp [step,hf,Instruction.execute,hcount,Cell.nat?]
      refine ⟨[before,{before with pc:=origin+18}],rfl,rfl,List.isChain_pair.mpr hs,?_⟩
      simpa using time_le_length program [before,{before with pc:=origin+18}]
  | succ count ih =>
      intro before pointer hpc haddress hcount hone
      let start : State := {before with pc:=origin+2}
      let returned : State := {baseRowWritesResult start pointer (count+1) with pc:=origin+1}
      have hf : program[before.pc]?=some (.branchZero .index (origin+18) (origin+2)) := by
        rw [hpc]
        exact hcode 1 (by rw [baseRowCode_length]; omega)
      have hs : step program input before=some start := by
        simp [step,hf,Instruction.execute,hcount,Cell.nat?,start]
      obtain ⟨body,hh,hl,hc,ht⟩ := baseRowBody_trace program input origin hcode start pointer (count+1)
        rfl haddress hcount hone
      have hindex : returned.register .index=.natural count := by simp [returned,baseRowWritesResult]
      have hpointer : returned.register .address=.natural (pointer+6) := by simp [returned,baseRowWritesResult]
      have hflag : returned.register .flag=.natural 1 := by simp [returned,baseRowWritesResult,start,hone]
      obtain ⟨later,lh,ll,lc,lt⟩ := ih returned (pointer+6) rfl hpointer hindex hflag
      have first := joinTrace_spec program input [before,start] body before start returned 30 255 rfl rfl hh hl
        (List.isChain_pair.mpr hs) hc (by simpa using time_le_length program [before,start]) ht
      have whole := joinTrace_spec program input (joinTrace [before,start] body) later before returned
        (baseRowLoopResult origin count returned (pointer+6)) (30+255) (300*count+30)
        first.1 first.2.1 lh ll first.2.2.1 lc first.2.2.2 lt
      refine ⟨joinTrace (joinTrace [before,start] body) later,whole.1,whole.2.1,whole.2.2.1,?_⟩
      have hw := whole.2.2.2
      omega

end PDCompute.Solver
