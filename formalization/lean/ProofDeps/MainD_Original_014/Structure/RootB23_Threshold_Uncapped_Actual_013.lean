module
public import Structure.RootB23_Threshold_Uncapped_Recovery_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section
namespace RootB23.Threshold.Uncapped.Actual
open PaperProofs.Common.Native.RationalControllerComputation

def joint : Machine 1582 := PSTRTMSeq005.seqMachine PSTRTMThresholdDynamicCap245.dynamicMachine Recovery.code

/-- TRUE1365 really HALTs with its existing quarter. FALSE1330 uses the
real Seq005 write-self transfer to the complete q-recovery suffix. This
one finite table is fixed before every q; q never selects machine code. -/
def code : Machine 1582 := fun q symbol => if q.val=1365 then none else joint q symbol

private theorem seq_value_right {a b : Nat} (first : Machine a) (second : Machine b)
    (label : Fin (b+1)) (symbol : Bool) :
    PSTRTMSeq005.seqMachine first second (PSTRTMSeq005.rightLabel (a:=a) label) symbol =
      (second label symbol).map (fun (next,statement) =>
        (PSTRTMSeq005.rightLabel (a:=a) next,statement)) := by
  simp only [PSTRTMSeq005.seqMachine,PSTRTMSeq005.rightLabel,
    show ¬a+1+label.val < a+1 by omega,↓reduceDIte,Nat.add_sub_cancel_left,Fin.eta]

theorem dynamic_true_halt (symbol : Bool) :
    PSTRTMThresholdDynamicCap245.dynamicMachine (1365 : Fin 1366) symbol = none := by
  change PSTRTMSeq005.seqMachine _ _ (PSTRTMSeq005.rightLabel (a:=1314) (50:Fin 51)) symbol = none
  rw [seq_value_right]
  have branch : PSTRTMThresholdCapBranch244.branchMachine (50:Fin 51) symbol = none := by
    simp only [PSTRTMThresholdCapBranch244.branchMachine,
      show (50:Fin 51).val ≠ 15 by decide,ite_false]
    change PSTRTMSeq005.seqMachine _ _ (PSTRTMSeq005.rightLabel (a:=15) (34:Fin 35)) symbol = none
    rw [seq_value_right]
    rfl
  rw [branch,Option.map_none]

theorem dynamic_false_halt (symbol : Bool) :
    PSTRTMThresholdDynamicCap245.dynamicMachine (1330 : Fin 1366) symbol = none := by
  change PSTRTMSeq005.seqMachine _ _ (PSTRTMSeq005.rightLabel (a:=1314) (15:Fin 51)) symbol = none
  rw [seq_value_right]
  have branch : PSTRTMThresholdCapBranch244.branchMachine (15:Fin 51) symbol = none := by
    simp only [PSTRTMThresholdCapBranch244.branchMachine,
      show (15:Fin 51).val = 15 by decide,ite_true]
  rw [branch,Option.map_none]

theorem dynamic_true_step (before : MachineState 1365) (atTrue : before.q.val=1365) :
    Turing.TM0.step PSTRTMThresholdDynamicCap245.dynamicMachine before = none := by
  cases before with
  | mk label tape =>
    have same : label = (1365 : Fin 1366) := Fin.ext atTrue
    subst label
    simp only [Turing.TM0.step,dynamic_true_halt,Option.map_none]

theorem code_true_step (before : MachineState 1582) (atTrue : before.q.val=1365) :
    Turing.TM0.step code before = none := by
  cases before with
  | mk label tape =>
    change label.val=1365 at atTrue
    simp only [Turing.TM0.step,code,atTrue,ite_true,Option.map_none]

theorem step_away (before : MachineState 1582) (away : before.q.val≠1365) :
    Turing.TM0.step code before = Turing.TM0.step joint before := by
  cases before
  simp only [Turing.TM0.step,code,away,ite_false]

theorem left_some (before after : MachineState 1365)
    (edge : Turing.TM0.step PSTRTMThresholdDynamicCap245.dynamicMachine before = some after) :
    Turing.TM0.step code (PSTRTMSeq005.leftCfg (b:=216) before) =
      some (PSTRTMSeq005.leftCfg (b:=216) after) := by
  have away : (PSTRTMSeq005.leftCfg (b:=216) before).q.val ≠ 1365 := by
    intro same
    have halted := dynamic_true_step before same
    rw [halted] at edge
    contradiction
  rw [step_away _ away]
  unfold joint
  rw [PSTRTMSeq005.seq_step_left,edge]

theorem right_step (before : MachineState 216) :
    Turing.TM0.step code (PSTRTMSeq005.rightCfg (a:=1365) before) =
      (Turing.TM0.step Recovery.code before).map (PSTRTMSeq005.rightCfg (a:=1365)) := by
  have away : (PSTRTMSeq005.rightCfg (a:=1365) before).q.val ≠ 1365 := by
    change 1366+before.q.val ≠ 1365
    omega
  rw [step_away _ away]
  exact PSTRTMSeq005.seq_step_right _ _ _

def trueTrace (front : List (MachineState 1365)) : List (MachineState 1582) :=
  front.map (PSTRTMSeq005.leftCfg (b:=216))
def falseTrace (front : List (MachineState 1365)) (later : List (MachineState 216)) : List (MachineState 1582) :=
  trueTrace front++later.map (PSTRTMSeq005.rightCfg (a:=1365))
def trueFinal (q : Rat) : MachineState 1582 :=
  PSTRTMSeq005.leftCfg (b:=216) (PSTRTMThresholdDynamicCap245.final q)
def falseFinal (q : Rat) : MachineState 1582 := PSTRTMSeq005.rightCfg (a:=1365)
  (⟨216,Turing.Tape.mk₁ (encodeDatum (.rational q))⟩ : MachineState 216)
def final (q : Rat) : MachineState 1582 := if (1/4 : Rat) ≤ q then trueFinal q else falseFinal q
def finalTape (q : Rat) : Turing.Tape Bool := if (1/4 : Rat) ≤ q then
  Turing.Tape.mk₂ (PSTRTMThresholdBReblock195.savedLeft q 1) (encodeDatum (.rational (1/4 : Rat)))
  else Turing.Tape.mk₁ (encodeDatum (.rational q))

theorem true_runs (q : Rat) (hq : 0 < q) (capped : (1/4 : Rat) ≤ q)
    (front : List (MachineState 1365))
    (actual : Runs PSTRTMThresholdDynamicCap245.dynamicMachine (encode [.rational q,.natural 1]) front
      (PSTRTMThresholdDynamicCap245.final q)) :
    Runs code (encode [.rational q,.natural 1]) (trueTrace front) (trueFinal q) := by
  apply PSTRTMTrace002.runs_of_chain
  · simp only [trueTrace,List.head?_map,actual.1,Option.map_some,
      PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Turing.TM0.init]
    rfl
  · apply (List.isChain_map _).mpr
    exact actual.2.1.imp (fun _ _ edge => left_some _ _ edge)
  · simp only [trueTrace,trueFinal,List.getLast?_map,actual.2.2.1,Option.map_some]
  · apply code_true_step
    change (PSTRTMThresholdDynamicCap245.final q).q.val = 1365
    rw [PSTRTMThresholdDynamicCap245.final_control q hq]
    simp only [capped,ite_true]

theorem false_runs (q : Rat) (hq : 0 < q) (uncapped : q < 1/4)
    (front : List (MachineState 1365)) (later : List (MachineState 216))
    (firstRun : Runs PSTRTMThresholdDynamicCap245.dynamicMachine (encode [.rational q,.natural 1]) front
      (PSTRTMThresholdDynamicCap245.final q))
    (secondRun : PSTRTMSeq005.RunsFrom Recovery.code ⟨0,(PSTRTMThresholdDynamicCap245.final q).Tape⟩
      later ⟨216,Turing.Tape.mk₁ (encodeDatum (.rational q))⟩) :
    Runs code (encode [.rational q,.natural 1]) (falseTrace front later) (falseFinal q) := by
  have common := PSTRTMSeq005.seq_runs PSTRTMThresholdDynamicCap245.dynamicMachine Recovery.code
    (encode [.rational q,.natural 1]) (PSTRTMThresholdDynamicCap245.final q)
    (⟨216,Turing.Tape.mk₁ (encodeDatum (.rational q))⟩ : MachineState 216) front later firstRun secondRun
  apply PSTRTMTrace002.runs_of_chain
  · exact common.1
  · apply List.IsChain.append
    · apply (List.isChain_map _).mpr
      exact firstRun.2.1.imp (fun _ _ edge => left_some _ _ edge)
    · apply (List.isChain_map _).mpr
      apply secondRun.2.1.imp
      intro before after edge
      simp only [right_step,edge,Option.map_some]
    · intro before hb after ha
      simp only [trueTrace,List.getLast?_map,firstRun.2.2.1,Option.map_some,Option.mem_some_iff] at hb
      simp only [List.head?_map,secondRun.1,Option.map_some,Option.mem_some_iff] at ha
      subst before
      subst after
      have away : (PSTRTMSeq005.leftCfg (b:=216) (PSTRTMThresholdDynamicCap245.final q)).q.val ≠ 1365 := by
        change (PSTRTMThresholdDynamicCap245.final q).q.val ≠ 1365
        rw [PSTRTMThresholdDynamicCap245.final_control q hq]
        simp only [not_le.mpr uncapped,ite_false]
        decide
      rw [step_away _ away]
      unfold joint
      rw [PSTRTMSeq005.seq_step_left,firstRun.2.2.2.1]
  · exact common.2.2.1
  · unfold falseFinal
    rw [right_step,secondRun.2.2.2,Option.map_none]

theorem final_tape (q : Rat) (hq : 0 < q) : (final q).Tape = finalTape q := by
  by_cases capped : (1/4 : Rat) ≤ q
  · simp only [final,finalTape,capped,ite_true,trueFinal,PSTRTMSeq005.leftCfg]
    rw [PSTRTMThresholdDynamicCap245.final_tape q hq]
    simp only [capped,ite_true]
  · simp only [final,finalTape,capped,ite_false,falseFinal,PSTRTMSeq005.rightCfg]

theorem final_right (q : Rat) (hq : 0 < q) :
    (final q).Tape.right₀ = Turing.ListBlank.mk (encodeDatum (.rational (min (1/4 : Rat) q))) := by
  rw [final_tape q hq]
  by_cases capped : (1/4 : Rat) ≤ q
  · simp only [finalTape,capped,ite_true,min_eq_left capped,Turing.Tape.mk₂,Turing.Tape.mk'_right₀]
  · simp only [finalTape,capped,ite_false,min_eq_right (le_of_not_ge capped),
      Turing.Tape.mk₁,Turing.Tape.mk₂,Turing.Tape.mk'_right₀]

private theorem scale_cube (input : Nat) : input+1 ≤ (input+2)^3 := by
  have positive : 1 ≤ input+2 := by omega
  have cube := Nat.pow_le_pow_right positive (by decide : 1 ≤ 3)
  simp only [pow_one] at cube
  omega

/-- Original q-only eligibility, ONE fixed Bool table, exact TRUE/FALSE
whole-Tape endpoints and ONE actual original-input trace. All resources
include the real branch transfer, recovery, serialization and erasures. -/
theorem original_minquarter_contract (q : Rat) (hq : 0 < q) :
    ∃ states, Runs code (encode [.rational q,.natural 1]) states (final q) ∧
      states.length ≤ 134217728*(Restore.inputSize q+2)^3 ∧
      ∀ clock, visitedSpace code (Restore.inputSize q) (states.take clock) ≤
        536870912*(Restore.inputSize q+2)^3 := by
  obtain ⟨front,firstRun,firstTime,_oldSpace⟩ := PSTRTMThresholdDynamicCap245.original_dynamicCap_contract q hq
  have hs : 1 ≤ Restore.inputSize q+2 := by omega
  have squareCube : (Restore.inputSize q+2)^2 ≤ (Restore.inputSize q+2)^3 :=
    Nat.pow_le_pow_right hs (by decide : 2 ≤ 3)
  have build : ∃ states, Runs code (encode [.rational q,.natural 1]) states (final q) ∧
      states.length ≤ 134217728*(Restore.inputSize q+2)^3 := by
    by_cases capped : (1/4 : Rat) ≤ q
    · refine ⟨trueTrace front,?_,?_⟩
      · simpa only [final,capped,ite_true] using true_runs q hq capped front firstRun
      · simp only [trueTrace,List.length_map]
        change front.length ≤ 67108864*(Restore.inputSize q+2)^3 at firstTime
        omega
    · have uncapped : q < 1/4 := lt_of_not_ge capped
      obtain ⟨later,secondRun,secondTime⟩ := Recovery.false_suffix_contract q hq uncapped
      refine ⟨falseTrace front later,?_,?_⟩
      · simpa only [final,capped,ite_false] using false_runs q hq uncapped front later firstRun secondRun
      · simp only [falseTrace,trueTrace,List.length_append,List.length_map]
        change front.length ≤ 67108864*(Restore.inputSize q+2)^3 at firstTime
        omega
  obtain ⟨states,actual,time⟩ := build
  refine ⟨states,actual,time,?_⟩
  intro clock
  have bound := PSTRTMTrace002.visitedSpace_le code (Restore.inputSize q) (states.take clock)
  have taken : (states.take clock).length ≤ states.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  have original := scale_cube (Restore.inputSize q)
  omega

theorem original_minquarter_computes (q : Rat) (hq : 0 < q) :
    computes code (encode [.rational q,.natural 1])
      (encodeDatum (.rational (min (1/4 : Rat) q)))
      (134217728*(Restore.inputSize q+2)^3) (536870912*(Restore.inputSize q+2)^3) := by
  obtain ⟨states,actual,time,space⟩ := original_minquarter_contract q hq
  refine ⟨states,final q,actual,final_right q hq,time,?_⟩
  simpa only [List.take_length,Restore.inputSize] using space states.length

end RootB23.Threshold.Uncapped.Actual
