module
public import Common.PSTR_TM_ThresholdCappedDatum_243

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapBranch244
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005

/-! Actual conditional continuation: FALSE15 really HALTs, while TRUE14
continues to the canonical quarter writer through a charged transfer.
It therefore never overwrites an uncapped value's B scratch field.
This is the fixed code for the branch, not a host-selected machine. -/

def branchMachine : Machine 50 := fun q symbol =>
  if q.val = 15 then none else
    seqMachine PSTRTMThresholdCapReturn240.returnMachine PSTRTMThresholdCapLiteral242.quarterMachine q symbol

theorem step_away (before : MachineState 50) (away : before.q.val ≠ 15) :
    Turing.TM0.step branchMachine before =
      Turing.TM0.step (seqMachine PSTRTMThresholdCapReturn240.returnMachine
        PSTRTMThresholdCapLiteral242.quarterMachine) before := by
  cases before
  simp only [Turing.TM0.step,branchMachine,away,ite_false]

theorem step_left_some (before after : MachineState 15)
    (edge : Turing.TM0.step PSTRTMThresholdCapReturn240.returnMachine before = some after) :
    Turing.TM0.step branchMachine (leftCfg (b := 34) before) = some (leftCfg (b := 34) after) := by
  have away : before.q.val ≠ 15 := by
    intro bad
    have same : before.q = 15 := Fin.ext bad
    have halted : Turing.TM0.step PSTRTMThresholdCapReturn240.returnMachine before = none := by
      simp [Turing.TM0.step,PSTRTMThresholdCapReturn240.returnMachine,same]
    rw [halted] at edge
    contradiction
  rw [step_away _ away,seq_step_left,edge]

theorem step_right (before : MachineState 34) :
    Turing.TM0.step branchMachine (rightCfg (a := 15) before) =
      (Turing.TM0.step PSTRTMThresholdCapLiteral242.quarterMachine before).map (rightCfg (a := 15)) := by
  have away : (rightCfg (a := 15) before).q.val ≠ 15 := by
    change 16+before.q.val ≠ 15
    omega
  rw [step_away _ away,seq_step_right]

def final (archive : List Bool) (n : Nat) : MachineState 50 :=
  if n ≤ 2 then rightCfg (a := 15) (PSTRTMThresholdCapLiteral242.state 34 archive
    (encodeDatum (.rational (1/4 : Rat))))
  else leftCfg (b := 34) (PSTRTMThresholdCapReturn240.state 15 archive (encodeDatum (.natural n)))

theorem final_tape (archive : List Bool) (n : Nat) :
    (final archive n).Tape = Turing.Tape.mk₂ archive
      (if n ≤ 2 then encodeDatum (.rational (1/4 : Rat)) else encodeDatum (.natural n)) := by
  unfold final
  split <;> rfl

theorem final_control (archive : List Bool) (n : Nat) : (final archive n).q.val =
    if n ≤ 2 then 50 else 15 := by
  unfold final
  split <;> rfl

/-- ALL canonical natural scratch values, including zero and arbitrary
width. TRUE50 produces quarter; FALSE15 keeps n exactly. The left archive
and original head position are preserved in both real branches. -/
theorem datum_branch_contract (archive : List Bool) (n : Nat) :
    ∃ trace,
      RunsFrom branchMachine ⟨0,Turing.Tape.mk₂ archive (encodeDatum (.natural n))⟩ trace (final archive n) ∧
      trace.length ≤ 45 := by
  obtain ⟨front,actual,time⟩ := PSTRTMThresholdCapReturn240.datum_return_contract n archive []
  simp only [List.append_nil] at actual
  by_cases small : n ≤ 2
  · simp only [small,ite_true] at actual
    have back := PSTRTMThresholdCapLiteral242.quarter_runsFrom archive n small
    let part := PSTRTMThresholdCapLiteral242.quarterTrace archive n
    have partHead : part.head? = some (PSTRTMThresholdCapLiteral242.state 0 archive
        (encodeDatum (.natural n))) := back.1
    let trace := front.map (leftCfg (b := 34)) ++ part.map (rightCfg (a := 15))
    have combined := seq_runsFrom PSTRTMThresholdCapReturn240.returnMachine
      PSTRTMThresholdCapLiteral242.quarterMachine
      (PSTRTMThresholdCapReturn240.state 0 archive (encodeDatum (.natural n)))
      (PSTRTMThresholdCapReturn240.state 14 archive (encodeDatum (.natural n)))
      (PSTRTMThresholdCapLiteral242.state 34 archive (encodeDatum (.rational (1/4 : Rat))))
      front part actual back
    refine ⟨trace,?_,?_⟩
    · refine ⟨combined.1,?_,?_,?_⟩
      · apply List.IsChain.append
        · apply (List.isChain_map _).mpr
          exact actual.2.1.imp (fun _ _ edge => step_left_some _ _ edge)
        · apply (List.isChain_map _).mpr
          apply back.2.1.imp
          intro before after edge
          simp only [step_right,edge,Option.map_some]
        · intro before hb after ha
          simp only [List.getLast?_map,actual.2.2.1,Option.map_some,Option.mem_some_iff] at hb
          simp only [List.head?_map,partHead,Option.map_some,Option.mem_some_iff] at ha
          subst before
          subst after
          have away : (leftCfg (b := 34) (PSTRTMThresholdCapReturn240.state 14 archive
              (encodeDatum (.natural n)))).q.val ≠ 15 := by
            change (14 : Nat) ≠ 15
            decide
          rw [step_away _ away,seq_step_left,actual.2.2.2]
          rfl
      · simpa only [final,small,ite_true] using combined.2.2.1
      · simp only [final,small,ite_true,step_right,back.2.2.2,Option.map_none]
    · have count : part.length = 35 := PSTRTMThresholdCapLiteral242.quarter_length _ _
      simp only [trace,List.length_append,List.length_map]
      omega
  · simp only [small,ite_false] at actual
    let trace := front.map (leftCfg (b := 34))
    refine ⟨trace,?_,?_⟩
    · refine ⟨?_,?_,?_,?_⟩
      · calc
          trace.head? = some (leftCfg (b := 34) (PSTRTMThresholdCapReturn240.state 0 archive
            (encodeDatum (.natural n)))) := by
              simp only [trace,List.head?_map,actual.1,Option.map_some]
          _ = some ⟨0,Turing.Tape.mk₂ archive (encodeDatum (.natural n))⟩ := rfl
      · apply (List.isChain_map _).mpr
        exact actual.2.1.imp (fun _ _ edge => step_left_some _ _ edge)
      · simp only [trace,List.getLast?_map,actual.2.2.1,Option.map_some,final,small,ite_false]
      · simp [final,small,Turing.TM0.step,branchMachine,leftCfg,leftLabel,
          PSTRTMThresholdCapReturn240.state]
    · simpa only [trace,List.length_map] using time.trans (by decide : 10 ≤ 45)

theorem branch_prefix_space (archive : List Bool) (n inputLength : Nat) :
    ∃ trace,
      RunsFrom branchMachine ⟨0,Turing.Tape.mk₂ archive (encodeDatum (.natural n))⟩ trace (final archive n) ∧
      trace.length ≤ 45 ∧
      ∀ clock, visitedSpace branchMachine inputLength (trace.take clock) ≤ inputLength+91 := by
  obtain ⟨trace,actual,time⟩ := datum_branch_contract archive n
  refine ⟨trace,actual,time,?_⟩
  intro clock
  have hs := PSTRTMTrace002.visitedSpace_le branchMachine inputLength (trace.take clock)
  have hl : (trace.take clock).length ≤ trace.length := by
    simp only [List.length_take]
    exact Nat.min_le_right _ _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdCapBranch244
