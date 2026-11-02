module
public import Structure.RootB23_Threshold_ReturnDispatch_021

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnActual
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

def badRight (risk : Rat) (depth : ℕ) (y : Rat) (right : ℕ) : List Bool :=
  Spatial.MulCap.output (FactorSource.factorValue risk depth : Rat) y++
    List.replicate (right+1-(Spatial.MulCap.output (FactorSource.factorValue risk depth : Rat) y).length) false
def postTape (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ) : Tape Bool :=
  Tape.mk₂ (PA17TMRatArithmeticFrame005.windowPrefix left
      (ListBlank.mk (Spatial.MulCap.oldLeft (FactorSource.factorValue risk depth : Rat) y))++
      ReturnBank.archive (BarePacket.west risk depth) (FactorSource.factorValue risk depth : Rat) y)
    (badRight risk depth y right)
def east (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ) : List Bool :=
  if (1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y then
    ReturnAnchor.trueEast ((FactorSource.factorValue risk depth : Rat)*y) left (badRight risk depth y right)
  else List.replicate left false++badRight risk depth y right
def finalTape (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ) : Tape Bool :=
  Tape.mk₂ (false::ReturnBank.bArchive risk depth) (ReturnBank.bRight risk depth y (east risk depth y left right))
def time (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : ℕ :=
  left+10*PA17TMRatArithmeticParse002.fieldWidth (FactorSource.factorValue risk depth : Rat) y+
    2*(FactorSource.bDigits risk depth).length+96

/-- The same blockCfg with its fixed numerical codomain made explicit,
so trace-length rewriting does not depend on unfolding totalStates. -/
def liftCfg (phase : Fin 2) (state : MachineState 109) : MachineState 219 :=
  ⟨label (p:=1) (s:=109) phase state.q,state.Tape⟩

/-- Complete actual return from the framed postTape to the original B
DATA head. The same two-row finite table serves both cap branches, and
retains the branch in its distinct terminal control port for later far
copies. All current badRisk output cells survive on the same east tape. -/
theorem actual_run (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<(FactorSource.factorValue risk depth : Rat)*y)
    (room : ReturnCredit.spare (FactorSource.factorValue risk depth : Rat) y≤left) :
    ∃ trace, PSTRTMSeq005.RunsFrom ReturnDispatch.code
      ⟨ReturnDispatch.entry (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y)),
        postTape risk depth y left right⟩ trace
      ⟨ReturnDispatch.exitPort (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y)),
        finalTape risk depth y left right⟩ ∧ trace.length≤time risk depth y left := by
  let x:=(FactorSource.factorValue risk depth : Rat)
  let base:=BarePacket.west risk depth
  let arc:=ReturnBank.innerArchive base x y
  let out:=badRight risk depth y right
  by_cases capped : (1/4 : Rat)≤x*y
  · have choice : decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y)=true := by
      change decide ((1/4 : Rat)≤x*y)=true
      simp only [capped,decide_true]
    have entry_eq : ReturnDispatch.entry (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y))=
        ReturnDispatch.entryTrue := (congrArg ReturnDispatch.entry choice).trans rfl
    have exit_eq : ReturnDispatch.exitPort (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y))=
        ReturnDispatch.exitTrue := (congrArg ReturnDispatch.exitPort choice).trans rfl
    have complete : (PSTRTMThresholdBReblock195.savedLeft (x*y) 1).length≤left := by
      have fits:=(ReturnCredit.oldLeft_fits x y positive).trans room
      simpa only [Spatial.MulCap.oldLeft,capped,ite_true] using fits
    have first:=ReturnAnchor.true_bounded arc out (x*y) left complete
    have second:=ReturnBank.actual_bounded risk depth y (ReturnAnchor.trueEast (x*y) left out)
    have actual:=first.seq second
    have port : PSTRTMSeq005.rightLabel (a:=38) (70 : Fin 71)=(109 : Fin 110) := by decide
    rw [port] at actual
    have bounded : BoundedRun ReturnDispatch.trueCode (postTape risk depth y left right) 109
        (finalTape risk depth y left right) (time risk depth y left) := by
      simpa only [ReturnDispatch.trueCode,postTape,finalTape,east,Spatial.MulCap.oldLeft,
        capped,ite_true,ReturnBank.archive,x,base,arc,out] using actual.mono (by dsimp only [time];omega)
    obtain ⟨part,run,fee⟩:=bounded
    have atRow : PSTRTMSeq005.RunsFrom (ReturnDispatch.rows (1 : Fin 2))
        ⟨0,postTape risk depth y left right⟩ part ⟨109,finalTape risk depth y left right⟩ := by
      simpa only [ReturnDispatch.rows,show (1 : Fin 2).val≠0 by decide,ite_false] using run
    have lifted:=block_runsFrom ReturnDispatch.rows ReturnDispatch.ports (1 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (1 : Fin 2)),?_,?_⟩
    · rw [entry_eq,exit_eq]
      exact lifted
    · rw [List.length_map]
      exact fee
  · have choice : decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y)=false := by
      change decide ((1/4 : Rat)≤x*y)=false
      simp only [capped,decide_false]
    have entry_eq : ReturnDispatch.entry (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y))=
        ReturnDispatch.entryFalse := (congrArg ReturnDispatch.entry choice).trans rfl
    have exit_eq : ReturnDispatch.exitPort (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y))=
        ReturnDispatch.exitFalse := (congrArg ReturnDispatch.exitPort choice).trans rfl
    have outHead : out=true::out.tail := rfl
    have first:=ReturnAnchor.false_bounded arc out.tail left
    rw [←outHead] at first
    have second:=ReturnBank.actual_bounded risk depth y (List.replicate left false++out)
    have actual:=first.seq second
    have port : PSTRTMSeq005.rightLabel (a:=1) (70 : Fin 71)=(72 : Fin 73) := by decide
    rw [port] at actual
    have blankPrefix : PA17TMRatArithmeticFrame005.windowPrefix left (ListBlank.mk ([] : List Bool))=
        List.replicate left false := by
      simpa only [List.length_nil,Nat.sub_zero,List.nil_append] using
        PA17TMRatArithmeticFrame005.windowPrefix_mk_of_length left [] (Nat.zero_le left)
    have bounded : BoundedRun ReturnDispatch.falseCode (postTape risk depth y left right) 72
        (finalTape risk depth y left right) (time risk depth y left) := by
      simpa only [ReturnDispatch.falseCode,postTape,finalTape,east,Spatial.MulCap.oldLeft,
        capped,ite_false,blankPrefix,ReturnBank.archive,x,base,arc,out] using actual.mono (by dsimp only [time];omega)
    have padded:=PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 72≤109) bounded
    obtain ⟨part,run,fee⟩:=padded
    have atRow : PSTRTMSeq005.RunsFrom (ReturnDispatch.rows (0 : Fin 2))
        ⟨0,postTape risk depth y left right⟩ part
        ⟨padLabel (by decide : 72≤109) (72 : Fin 73),finalTape risk depth y left right⟩ := by
      simpa only [ReturnDispatch.rows,Fin.val_zero,ite_true] using run
    have lifted:=block_runsFrom ReturnDispatch.rows ReturnDispatch.ports (0 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (0 : Fin 2)),?_,?_⟩
    · rw [entry_eq,exit_eq]
      exact lifted
    · rw [List.length_map]
      exact fee

/-- Direct Window029 consumer: its exact actual nested HALT label selects
this fixed return entry. left/right remain proof credits; neither is
encoded on the tape or passed to the finite control as an answer/fuel. -/
theorem actual_contract (prefixCap : ℕ) (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<(FactorSource.factorValue risk depth : Rat)*y)
    (room : ReturnCredit.spare (FactorSource.factorValue risk depth : Rat) y≤left) :
    ∃ trace,
      ReturnDispatch.dispatch prefixCap
        (PSTRTMSeq005.rightLabel (a:=prefixCap) (Spatial.MulCap.final (FactorSource.factorValue risk depth : Rat) y).q)=
        some (ReturnDispatch.entry (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y))) ∧
      PSTRTMSeq005.RunsFrom ReturnDispatch.code
        ⟨ReturnDispatch.entry (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y)),
          postTape risk depth y left right⟩ trace
        ⟨ReturnDispatch.exitPort (decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y)),
          finalTape risk depth y left right⟩ ∧
      trace.length≤time risk depth y left ∧
      ∀ chargedLength clock, visitedSpace ReturnDispatch.code chargedLength (trace.take clock)≤
        chargedLength+2*time risk depth y left+1 := by
  obtain ⟨trace,actual,fee⟩:=actual_run risk depth y left right positive room
  refine ⟨trace,ReturnDispatch.actual_dispatch prefixCap _ _ positive,actual,fee,?_⟩
  intro chargedLength clock
  have space:=PSTRTMTrace002.visitedSpace_le ReturnDispatch.code chargedLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.ReturnActual
