module

public import Common.PSTR_SYM_CounterRound_031
public import Common.PSTR_SYM_CursorStages_049
public import Common.PSTR_WordBool_NativeTrace_006

/-! The real old machines are called with fixed finite labels. Initial
zero is tested before any borrow. Every old HALT-to-next-stage transfer is
a paid head-preserving WRITE. Every EOF-to-fieldBack connector performs
one actual RIGHT first. The TRUE suffix is a physical cell, not Tape EOF. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.RuntimeCounter.Round.Raw

open Turing
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMSeq005 PSTRTMIncrement009 PSTRTMRawNat010
open PSTRTMThresholdCountdownCode164 PSTRTMThresholdDepthZeroCode167
open PSTRTMThresholdDepthZeroRun168 PSTRSymbolicCounter
open PA17TMRatArithmeticParse002 PSTRSymbolicCursorCode PSTRSymbolicCursorStages

def packet (digits : List Bool) : List Bool := blocks digits++[false,false,true]

def endTape (digits : List Bool) : Tape Bool :=
  Tape.mk₂ (leftBlocks digits.reverse++[false]) [false,false,true]

def stableTape (digits : List Bool) : Tape Bool := Tape.mk₂ [false] (packet digits)

def rightBackMachine : Machine 7 := seqMachine footerMachine fieldBackMachine

def rightBackTrace (digits : List Bool) : List (MachineState 7) :=
  ([⟨0,endTape digits⟩,⟨1,(endTape digits).move .right⟩] : List (MachineState 1)).map
    (leftCfg (b := 5)) ++
  (fieldBackTrace [] digits [false,true]).map (rightCfg (a := 1))

def rightBackFinal (digits : List Bool) : MachineState 7 :=
  rightCfg (a := 1) (fieldBackFinal [] digits [false,true])

theorem end_right (digits : List Bool) :
    (endTape digits).move .right=
      Tape.mk₂ (false::(leftBlocks digits.reverse++[false])) [false,true] := by
  simp [endTape,Tape.mk₂]

theorem rightBack_runs (digits : List Bool) :
    RunsFrom rightBackMachine ⟨0,endTape digits⟩ (rightBackTrace digits) (rightBackFinal digits) := by
  apply seq_runsFrom footerMachine fieldBackMachine ⟨0,endTape digits⟩
    ⟨1,(endTape digits).move .right⟩ (fieldBackFinal [] digits [false,true])
    [⟨0,endTape digits⟩,⟨1,(endTape digits).move .right⟩] (fieldBackTrace [] digits [false,true])
  · refine ⟨rfl,?_,rfl,?_⟩
    · simp [List.isChain_cons_cons,TM0.step,footerMachine]
    · simp [TM0.step,footerMachine]
  · rw [end_right]
    exact fieldBack_runsFrom [] digits [false,true]

theorem rightBack_tape (digits : List Bool) : (rightBackFinal digits).Tape=stableTape digits := rfl

theorem rightBack_length (digits : List Bool) : (rightBackTrace digits).length=2*digits.length+7 := by
  simp only [rightBackTrace,List.length_append,List.length_map,List.length_cons,List.length_nil,
    fieldBackTrace_length]
  omega

inductive Label where
  | test : Fin 8 → Label
  | back : Bool → Fin 8 → Label
  | borrow : Fin 17 → Label
  | postBack : Bool → Fin 8 → Label
  | halt : Bool → Bool → Label
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.test 0⟩

def machine : TM0.Machine Bool Label := fun point symbol =>
  match point with
  | .test point => calledCode zeroMachine .test (fun point => .back (decide (point.val=6)) 0) point symbol
  | .back initialZero point => calledCode rightBackMachine (.back initialZero)
      (fun _ => if initialZero then .halt true true else .borrow 0) point symbol
  | .borrow point => calledCode counterRoundMachine .borrow
      (fun point => .postBack (decide (point.val=15)) 0) point symbol
  | .postBack newZero point => calledCode rightBackMachine (.postBack newZero)
      (fun _ => .halt false newZero) point symbol
  | .halt _ _ => none

def support : Finset Label := Finset.univ

theorem supports : TM0.Supports machine (support : Set Label) := by
  refine ⟨by simp [support],?_⟩
  intro _point _bit _next _op _edge _present
  exact Finset.mem_univ _

abbrev State := TM0.Cfg Bool Label

structure Path (before final : State) (budget : Nat) where
  trace : List State
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM0.step machine a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Path.append {before middle final : State} {a b : Nat}
    (front : Path before middle a) (back : Path middle final b) : Path before final (a+b-1) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]; rfl
  have size := congrArg List.length shape
  simp only [List.length_cons] at size
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.first]; rfl
  · exact PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain _ _ _
      front.last front.chain (shape.symm ▸ back.chain)
  · exact (PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_last _ _ _ front.last).trans
      (shape.symm ▸ back.last)
  · have h1 := front.count
    have h2 := back.count
    simp only [List.length_append]
    omega

def calledPath {states : Nat} (callee : Machine states)
    (tag finish : Fin (states+1) → Label)
    (code : ∀ point bit,machine (tag point) bit=calledCode callee tag finish point bit)
    (before final : MachineState states) (trace : List (MachineState states))
    (actual : RunsFrom callee before trace final) :
    Path (tagCfg tag before) ⟨finish final.q,final.Tape⟩ (trace.length+1) := by
  have part := called_endpoints machine callee tag finish code before final trace actual
  refine ⟨trace.map (tagCfg tag)++[⟨finish final.q,final.Tape⟩],?_,?_,?_,?_⟩
  · rw [List.head?_append,part.1]; rfl
  · apply List.IsChain.append part.2.1 (List.isChain_singleton _)
    intro before atLast after atFirst
    simp only [part.2.2.1,Option.mem_some_iff] at atLast
    simp only [List.head?_singleton,Option.mem_some_iff] at atFirst
    subst before
    subst after
    exact part.2.2.2.1
  · exact List.getLast?_append_cons _ _ []
  · simp only [List.length_append,List.length_map,List.length_cons,List.length_nil,Nat.le_refl]

def outputDigits (digits : List Bool) : List Bool :=
  if valueDigits digits=0 then digits else predDigits digits

def initial (digits : List Bool) : State := ⟨.test 0,stableTape digits⟩

def final (digits : List Bool) : State :=
  ⟨.halt (decide (valueDigits digits=0)) (decide (valueDigits digits≤1)),stableTape (outputDigits digits)⟩

theorem zero_test_flag (digits : List Bool) :
    decide ((PSTRTMThresholdDepthZeroRun168.final [] [] false digits [true]).q.val=6)=
      decide (valueDigits digits=0) := by
  have tested := seen_false_iff_value_zero digits
  cases seenEq : seen false digits <;>
    simp_all [PSTRTMThresholdDepthZeroRun168.final,PSTRTMThresholdDepthZeroCode167.state,haltLabel]

theorem test_path (digits : List Bool) :
    Nonempty (Path (initial digits)
      ⟨.back (decide (valueDigits digits=0)) 0,endTape digits⟩ (2*digits.length+4)) := by
  let part := calledPath zeroMachine Label.test (fun point => .back (decide (point.val=6)) 0)
    (by intro point bit; rfl) _ _ _ (zero_runsFrom [] digits [true])
  have physical : (PSTRTMThresholdDepthZeroRun168.final [] [] false digits [true]).Tape=endTape digits := by
    simp [PSTRTMThresholdDepthZeroRun168.final,PSTRTMThresholdDepthZeroCode167.state,
      contextLeft,endTape]
  have endpoint : (⟨.back (decide ((PSTRTMThresholdDepthZeroRun168.final [] [] false digits [true]).q.val=6)) 0,
      (PSTRTMThresholdDepthZeroRun168.final [] [] false digits [true]).Tape⟩ : State)=
      ⟨.back (decide (valueDigits digits=0)) 0,endTape digits⟩ := by
    rw [zero_test_flag,physical]
  have last : part.trace.getLast?=some ⟨.back (decide (valueDigits digits=0)) 0,endTape digits⟩ := by
    exact part.last.trans (congrArg some endpoint)
  refine ⟨⟨part.trace,part.first,part.chain,last,?_⟩⟩
  have bound := part.count
  have length := zero_length [] [] false digits [true]
  omega

theorem back_path (digits : List Bool) (initialZero : Bool) :
    Nonempty (Path ⟨.back initialZero 0,endTape digits⟩
      ⟨if initialZero then .halt true true else .borrow 0,stableTape digits⟩ (2*digits.length+8)) := by
  let part := calledPath rightBackMachine (.back initialZero)
    (fun _ => if initialZero then .halt true true else .borrow 0)
    (by intro point bit; rfl) _ _ _ (rightBack_runs digits)
  refine ⟨⟨part.trace,part.first,part.chain,part.last,?_⟩⟩
  have bound := part.count
  have length := rightBack_length digits
  omega

theorem borrow_path (digits : List Bool) (positive : true∈digits) :
    Nonempty (Path ⟨.borrow 0,stableTape digits⟩
      ⟨.postBack (decide (valueDigits digits=1)) 0,endTape (predDigits digits)⟩ (8*(digits.length+1)+1)) := by
  let part := calledPath counterRoundMachine Label.borrow (fun point => .postBack (decide (point.val=15)) 0)
    (by intro point bit; rfl) _ _ _ (counterRound_runsFrom [] digits [true] positive)
  have flag : decide ((counterRoundFinal [] digits [true]).q.val=15)=decide (valueDigits digits=1) :=
    decide_eq_decide.mpr (counterRound_zero_port [] digits [true] positive)
  have endpoint : (⟨.postBack (decide ((counterRoundFinal [] digits [true]).q.val=15)) 0,
      (counterRoundFinal [] digits [true]).Tape⟩ : State)=
      ⟨.postBack (decide (valueDigits digits=1)) 0,endTape (predDigits digits)⟩ := by
    rw [flag,counterRound_final_tape]
    rfl
  have last : part.trace.getLast?=some
      ⟨.postBack (decide (valueDigits digits=1)) 0,endTape (predDigits digits)⟩ := by
    exact part.last.trans (congrArg some endpoint)
  refine ⟨⟨part.trace,part.first,part.chain,last,?_⟩⟩
  have bound := part.count
  have time := counterRound_time_le [] digits [true] positive
  omega

theorem post_path (digits : List Bool) (newZero : Bool) :
    Nonempty (Path ⟨.postBack newZero 0,endTape digits⟩
      ⟨.halt false newZero,stableTape digits⟩ (2*digits.length+8)) := by
  let part := calledPath rightBackMachine (.postBack newZero) (fun _ => .halt false newZero)
    (by intro point bit; rfl) _ _ _ (rightBack_runs digits)
  refine ⟨⟨part.trace,part.first,part.chain,part.last,?_⟩⟩
  have bound := part.count
  have length := rightBack_length digits
  omega

theorem actual (digits : List Bool) :
    ∃ trace : List State,(trace.head?=some (initial digits) ∧
      trace.IsChain (fun a b => TM0.step machine a=some b) ∧
      trace.getLast?=some (final digits) ∧ TM0.step machine (final digits)=none) ∧
      trace.length≤32*(digits.length+1) := by
  obtain ⟨test⟩ := test_path digits
  by_cases zero : valueDigits digits=0
  · obtain ⟨back⟩ := back_path digits true
    have test' : Nonempty (Path (initial digits) ⟨.back true 0,endTape digits⟩ (2*digits.length+4)) := by
      simpa only [zero,decide_true] using (⟨test⟩ : Nonempty _)
    obtain ⟨test⟩ := test'
    let whole := test.append back
    refine ⟨whole.trace,⟨whole.first,whole.chain,?_,?_⟩,?_⟩
    · simpa [final,outputDigits,zero] using whole.last
    · simp [machine,final,zero,TM0.step]
    · have count := whole.count
      omega
  · have positive := has_true_of_value_pos digits (Nat.pos_of_ne_zero zero)
    obtain ⟨back⟩ := back_path digits false
    obtain ⟨borrow⟩ := borrow_path digits positive
    obtain ⟨post⟩ := post_path (predDigits digits) (decide (valueDigits digits=1))
    have test' : Nonempty (Path (initial digits) ⟨.back false 0,endTape digits⟩ (2*digits.length+4)) := by
      simpa only [zero,decide_false] using (⟨test⟩ : Nonempty _)
    obtain ⟨test⟩ := test'
    let whole := ((test.append back).append borrow).append post
    have flag : decide (valueDigits digits=1)=decide (valueDigits digits≤1) := by
      apply decide_eq_decide.mpr
      omega
    refine ⟨whole.trace,⟨whole.first,whole.chain,?_,?_⟩,?_⟩
    · simpa [final,outputDigits,zero,flag] using whole.last
    · simp [machine,final,TM0.step]
    · have count := whole.count
      have width := pred_length digits
      omega

noncomputable def finiteMachine : Machine support.card := PSTRSymbolicRelabel.finiteMachine machine support

noncomputable def finiteCfg (current : State) : MachineState support.card :=
  PSTRSymbolicRelabel.relabelCfg (PSTRSymbolicRelabel.finiteLabels support) current

theorem finite_step (current : State) :
    TM0.step finiteMachine (finiteCfg current)=(TM0.step machine current).map finiteCfg := by
  exact (PSTRSymbolicRelabel.relabel_step machine (support : Set Label)
    (PSTRSymbolicRelabel.finiteLabels support) (PSTRSymbolicRelabel.finiteDecode support)
    (PSTRSymbolicRelabel.finite_inverse support) current (Finset.mem_univ _)).symm

theorem finite_actual (digits : List Bool) :
    ∃ trace,RunsFrom finiteMachine (finiteCfg (initial digits)) trace (finiteCfg (final digits)) ∧
      trace.length≤32*(digits.length+1) := by
  obtain ⟨trace,run,time⟩ := actual digits
  refine ⟨trace.map finiteCfg,⟨?_,?_,?_,?_⟩,?_⟩
  · rw [List.head?_map,run.1]; rfl
  · apply (List.isChain_map _).mpr
    exact run.2.1.imp (fun before after edge => by rw [finite_step,edge]; rfl)
  · rw [List.getLast?_map,run.2.2.1]; rfl
  · rw [finite_step,run.2.2.2]; rfl
  · simpa only [List.length_map] using time

end RootB234.RuntimeCounter.Round.Raw
