module
public import Structure.RootB23_Threshold_ReturnDestination_029

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnFarActual
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

def branch (risk : Rat) (depth : ℕ) (y : Rat) : Bool :=
  decide ((1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y)
def product (risk : Rat) (depth : ℕ) (y : Rat) : Rat := (FactorSource.factorValue risk depth : Rat)*y
def core (capped : Bool) (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : List Bool :=
  ReturnBank.bRight risk depth y (ReturnRoute.bridge capped (product risk depth y) left++
    encodeDatum (.rational (ReturnRoute.result capped (product risk depth y))))

theorem marked_prefix (q : Rat) (tail : List Bool) :
    ReturnAnchor.markedSourceRight q tail=ReturnAnchor.markedSourceRight q []++tail := by
  simp only [ReturnAnchor.markedSourceRight,ReturnAnchor.depthRight,PSTRTMThresholdRiskMarkers232.markerTail,
    List.append_assoc,List.cons_append,List.nil_append]
theorem source_append (x y : Rat) (first last : List Bool) :
    ReturnBank.sourceRight x y (first++last)=ReturnBank.sourceRight x y first++last := by
  simp only [ReturnBank.sourceRight,ReturnBank.counterWord,PA17TMRatArithmeticFarLoad031.fieldWord,
    List.append_assoc,List.cons_append]
theorem bRight_append (risk : Rat) (depth : ℕ) (y : Rat) (first last : List Bool) :
    ReturnBank.bRight risk depth y (first++last)=ReturnBank.bRight risk depth y first++last := by
  rw [ReturnBank.bRight,source_append]
  simp only [ReturnBank.bRight,List.append_assoc,List.cons_append]

theorem actual_east (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ) :
    ReturnActual.east risk depth y left right=
      (ReturnRoute.bridge (branch risk depth y) (product risk depth y) left++
        encodeDatum (.rational (ReturnRoute.result (branch risk depth y) (product risk depth y))))++
      List.replicate (right+1-(Spatial.MulCap.output (FactorSource.factorValue risk depth : Rat) y).length) false := by
  by_cases capped : (1/4 : Rat)≤(FactorSource.factorValue risk depth : Rat)*y
  · have choice : branch risk depth y=true := by simp only [branch,capped,decide_true]
    rw [choice]
    simp only [ReturnActual.east,capped,ite_true,ReturnActual.badRight,Spatial.MulCap.output,min_eq_left capped]
    rw [ReturnAnchor.trueEast,marked_prefix]
    simp only [ReturnRoute.bridge,ReturnRoute.result,ReturnRoute.blank,product,List.append_assoc,List.cons_append]
  · have choice : branch risk depth y=false := by simp only [branch,capped,decide_false]
    rw [choice]
    have below : (FactorSource.factorValue risk depth : Rat)*y≤(1/4 : Rat) := le_of_not_ge capped
    simp only [ReturnActual.east,capped,ite_false,ReturnActual.badRight,Spatial.MulCap.output,min_eq_right below,
      ReturnRoute.bridge,ReturnRoute.result,product,List.append_assoc]

theorem field_core (capped : Bool) (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) :
    RoutedCopy.fieldWord
      (ReturnRoute.context capped (FactorSource.factorValue risk depth : Rat) y (product risk depth y) left)
      (FactorSource.bDigits risk depth) []=core capped risk depth y left++[false] := by
  simp only [RoutedCopy.fieldWord,ReturnRoute.context,core,ReturnBank.bRight,source_append,
    List.append_assoc,List.cons_append]

/-- Only the genuine infinite RIGHT tail is normalized here. Every
interior zero, marker, original field and cap scratch remains literal. -/
theorem actual_input (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ) :
    ReturnActual.finalTape risk depth y left right=
      Tape.mk₂ (false::ReturnBank.bArchive risk depth)
        (RoutedCopy.fieldWord
          (ReturnRoute.context (branch risk depth y) (FactorSource.factorValue risk depth : Rat) y (product risk depth y) left)
          (FactorSource.bDigits risk depth) []) := by
  rw [ReturnActual.finalTape,actual_east,bRight_append,field_core]
  change Tape.mk₂ (false::ReturnBank.bArchive risk depth)
      (core (branch risk depth y) risk depth y left++List.replicate _ false)=_
  simp only [Tape.mk₂,PA17TMDivisionTape005.blank_false_suffix,PSTRTMRawNat010.blank_append_false]

def rows (phase : Fin 2) : Machine 2380 := ReturnDestination.code (phase.val==1)
def ports (_phase : Fin 2) (_localLabel : Fin 2381) : Option (Fin 2 × Fin 2381) := none
def code : Machine 4761 := blockMachine rows ports
def entryFalse : Fin 4762 := label (p:=1) (s:=2380) 0 0
def entryTrue : Fin 4762 := label (p:=1) (s:=2380) 1 0
def exitFalse : Fin 4762 := label (p:=1) (s:=2380) 0 2380
def exitTrue : Fin 4762 := label (p:=1) (s:=2380) 1 2380
def entry (capped : Bool) : Fin 4762 := if capped then entryTrue else entryFalse
def exitPort (capped : Bool) : Fin 4762 := if capped then exitTrue else exitFalse
def dispatch (control : Fin 220) : Option (Fin 4762) :=
  if control.val=219 then some entryTrue else if control.val=72 then some entryFalse else none
theorem actual_dispatch (capped : Bool) : dispatch (ReturnDispatch.exitPort capped)=some (entry capped) := by
  cases capped <;> decide
def liftCfg (phase : Fin 2) (state : MachineState 2380) : MachineState 4761 :=
  ⟨label (p:=1) (s:=2380) phase state.q,state.Tape⟩
def finalTape (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : Tape Bool :=
  Tape.mk₂ (ReturnDestination.destinationLeft (branch risk depth y) (FactorSource.factorValue risk depth : Rat) y
    (product risk depth y) left (ReturnBank.bArchive risk depth) (FactorSource.bDigits risk depth))
    (PSTRTMIncrement009.blocks (FactorSource.bDigits risk depth))
def fee (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : ℕ :=
  ReturnDestination.fee (branch risk depth y) (FactorSource.factorValue risk depth : Rat) y
    (product risk depth y) left (FactorSource.bDigits risk depth)

/-- The single fixed two-row table consumes the SAME actual cap branch.
It starts at ReturnActual022's exact post-return tape and ends on a new
real B DATA field with genuinely blank RIGHT, suitable for199/209. -/
theorem actual_run (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<product risk depth y) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨entry (branch risk depth y),ReturnActual.finalTape risk depth y left right⟩ trace
      ⟨exitPort (branch risk depth y),finalTape risk depth y left⟩ ∧ trace.length≤fee risk depth y left := by
  have nonnegative : (0 : Rat)≤(FactorSource.factorValue risk depth : Rat) := Nat.cast_nonneg _
  have bounded:=ReturnDestination.bounded (branch risk depth y) (FactorSource.factorValue risk depth : Rat) y
    (product risk depth y) nonnegative (le_of_lt positive) left (ReturnBank.bArchive risk depth) (FactorSource.bDigits risk depth)
  rw [←actual_input risk depth y left right] at bounded
  obtain ⟨part,run,time⟩:=bounded
  cases found : branch risk depth y with
  | false=>
    have atRow : PSTRTMSeq005.RunsFrom (rows (0 : Fin 2))
        ⟨0,ReturnActual.finalTape risk depth y left right⟩ part ⟨2380,finalTape risk depth y left⟩ := by
      simpa only [found,rows,show ((0 : Fin 2).val==1)=false by decide,finalTape] using run
    have lifted:=block_runsFrom rows ports (0 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (0 : Fin 2)),?_,?_⟩
    · exact lifted
    · rw [List.length_map]
      simpa only [fee,found] using time
  | true=>
    have atRow : PSTRTMSeq005.RunsFrom (rows (1 : Fin 2))
        ⟨0,ReturnActual.finalTape risk depth y left right⟩ part ⟨2380,finalTape risk depth y left⟩ := by
      simpa only [found,rows,show ((1 : Fin 2).val==1)=true by decide,finalTape] using run
    have lifted:=block_runsFrom rows ports (1 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (1 : Fin 2)),?_,?_⟩
    · exact lifted
    · rw [List.length_map]
      simpa only [fee,found] using time

theorem actual_contract (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<product risk depth y) :
    ∃ trace, dispatch (ReturnDispatch.exitPort (branch risk depth y))=some (entry (branch risk depth y)) ∧
      PSTRTMSeq005.RunsFrom code
        ⟨entry (branch risk depth y),ReturnActual.finalTape risk depth y left right⟩ trace
        ⟨exitPort (branch risk depth y),finalTape risk depth y left⟩ ∧
      trace.length≤fee risk depth y left ∧
      ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock)≤chargedLength+2*fee risk depth y left+1 := by
  obtain ⟨trace,run,time⟩:=actual_run risk depth y left right positive
  refine ⟨trace,actual_dispatch _,run,time,?_⟩
  intro chargedLength clock
  have space:=PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.ReturnFarActual
