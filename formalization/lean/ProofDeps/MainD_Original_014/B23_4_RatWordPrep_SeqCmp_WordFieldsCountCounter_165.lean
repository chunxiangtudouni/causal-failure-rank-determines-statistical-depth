module

public import B23_4_RatWordPrep_SeqCmp_WordFieldsCountCalls_163
public import B23_4_RatWordPrep_SeqCmp_WordFieldsCounter_086

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFields.Count

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem clearPath_time (caller : Statement C) (bank : RatInput.Stack → List Bool) (memory : Store C) (cells : List Bool) :
    (clearPath caller bank memory cells).trace.length≤2*cells.length+2 := by
  induction cells generalizing memory with
  | nil => rfl
  | cons bit cells ih =>
    let next := clearState bank .clearCount (capture memory (some bit)) cells
    let edge : Segment caller (clearState bank .clearCount memory (bit::cells)) next :=
      ⟨[clearState bank .clearCount memory (bit::cells),next],rfl,
        List.isChain_cons_cons.mpr ⟨clear_bit caller bank memory bit cells,List.isChain_singleton _⟩,rfl⟩
    have joined := append_length_le edge (clearPath caller bank (capture memory (some bit)) cells)
    have tail := ih (capture memory (some bit))
    have edgeTime : edge.trace.length=2 := rfl
    change (edge.append (clearPath caller bank (capture memory (some bit)) cells)).trace.length≤_
    rw [edgeTime] at joined
    simp only [List.length_cons]
    omega

theorem actual_clear (caller : Statement C) (before : State C) (active : before.l=some .clearCount) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.round 0) ∧ final.var.2.2=before.var.2.2 ∧ final.stk 3=[] ∧
      (∀ slot,slot≠3 → final.stk slot=before.stk slot) ∧
      run.trace.length≤2*(before.stk 3).length+2 ∧ RatInput.occupied final.stk≤RatInput.occupied before.stk := by
  have shared : clearState before.stk .clearCount before.var (before.stk 3)=before := by
    unfold clearState
    rw [Function.update_eq_self,←active]
  let result := clearPath caller before.stk before.var (before.stk 3)
  let run : Segment caller before (clearState before.stk (.round 0) (capture before.var none) []) :=
    ⟨result.trace,result.first.trans (congrArg some shared),result.chain,result.last⟩
  refine ⟨_,run,rfl,rfl,rfl,?_,clearPath_time caller before.stk before.var (before.stk 3),?_⟩
  · intro slot untouched
    exact Function.update_of_ne untouched _ _
  · have erased := WordFinish.Resources.update_mass before.stk 3 []
    change RatInput.occupied (Function.update before.stk 3 [])≤_
    simp only [List.length_nil,Nat.add_zero] at erased
    omega

def countBuildWork (before : State C) (number : Nat) : Nat :=
  (before.stk 10).length+(before.stk 11).length+6*(PSTRTMNatValue017.rawPayload number).length+20

theorem actual_count_setup (caller : Statement C) (before : State C) (number : Nat)
    (active : before.l=some (.build 0)) (source : before.stk 3=NatField.packet number [])
    (scratch : before.stk 4=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.round 0) ∧ final.var.2.2=before.var.2.2 ∧
      final.stk 10=RootB234.RuntimeCounter.Round.Raw.packet (PSTRTMNatValue017.rawPayload number) ∧
      final.stk 11=[false] ∧ final.stk 4=[] ∧ final.stk 3=[] ∧
      (∀ slot,slot≠3 → slot≠4 → slot≠10 → slot≠11 → final.stk slot=before.stk slot) ∧
      run.trace.length≤countBuildWork before number ∧
      RatInput.occupied final.stk≤RatInput.occupied before.stk+pushCap caller*countBuildWork before number := by
  obtain ⟨middle,buildRun,port,context,counter,left,temp,frame,time⟩ :=
    WordFields.actual_build caller before number [] active source scratch
  have current : middle.stk 3=NatField.packet number [] := (frame 3 (by decide) (by decide) (by decide)).trans source
  obtain ⟨final,clearRun,finalPort,clearContext,empty3,clearFrame,clearTime,_clearMass⟩ := actual_clear caller middle port
  let whole := buildRun.append clearRun
  have total : whole.trace.length≤countBuildWork before number := by
    have clearSize : (middle.stk 3).length=2*(PSTRTMNatValue017.rawPayload number).length+2 := by
      rw [current,WordFinish.Resources.natural_packet_length]
      simp only [List.length_nil,Nat.add_zero]
    have joined := append_length_le buildRun clearRun
    rw [clearSize] at clearTime
    change (buildRun.append clearRun).trace.length≤_
    unfold countBuildWork
    omega
  have grow := WordFinish.Resources.trace_mass (pushCap caller) (pushes caller) whole.trace before
    (RatInput.occupied before.stk) whole.first whole.chain (Nat.le_refl _) final (List.mem_of_getLast? whole.last)
  refine ⟨final,whole,finalPort,clearContext.trans context,?_,?_,?_,empty3,?_,total,?_⟩
  · exact (clearFrame 10 (by decide)).trans counter
  · exact (clearFrame 11 (by decide)).trans left
  · exact (clearFrame 4 (by decide)).trans temp
  · intro slot n3 n4 n10 n11
    exact (clearFrame slot n3).trans (frame slot n4 n10 n11)
  · exact grow.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ total) _)

end B23_4_RatWordPrep.WordFields.Count
