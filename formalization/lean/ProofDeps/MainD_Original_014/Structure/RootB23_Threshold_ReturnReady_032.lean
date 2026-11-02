module
public import Structure.RootB23_Threshold_ReturnHeadroom_031

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnReady
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

def bodyCode (capped : Bool) : Machine 2620 := PSTRTMSeq005.seqMachine (ReturnDestination.code capped) ReturnHeadroom.code
def rows (phase : Fin 2) : Machine 2620 := bodyCode (phase.val==1)
def ports (_phase : Fin 2) (_localLabel : Fin 2621) : Option (Fin 2 × Fin 2621) := none
def code : Machine 5241 := blockMachine rows ports
def entryFalse : Fin 5242 := label (p:=1) (s:=2620) 0 0
def entryTrue : Fin 5242 := label (p:=1) (s:=2620) 1 0
def exitFalse : Fin 5242 := label (p:=1) (s:=2620) 0 2620
def exitTrue : Fin 5242 := label (p:=1) (s:=2620) 1 2620
def entry (capped : Bool) : Fin 5242 := if capped then entryTrue else entryFalse
def exitPort (capped : Bool) : Fin 5242 := if capped then exitTrue else exitFalse
def liftCfg (phase : Fin 2) (state : MachineState 2620) : MachineState 5241 :=
  ⟨label (p:=1) (s:=2620) phase state.q,state.Tape⟩
def archive (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : List Bool :=
  true::false::ReturnRoute.finish (ReturnFarActual.branch risk depth y) (FactorSource.factorValue risk depth : Rat) y
    (ReturnFarActual.product risk depth y) left (false::ReturnBank.bArchive risk depth) (FactorSource.bDigits risk depth)
def finalTape (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : Tape Bool :=
  Tape.mk₂ (List.replicate 9 false++archive risk depth y left) (PSTRTMIncrement009.blocks (FactorSource.bDigits risk depth))
def fee (risk : Rat) (depth : ℕ) (y : Rat) (left : ℕ) : ℕ :=
  ReturnFarActual.fee risk depth y left+80*(FactorSource.bDigits risk depth).length+192

/-- Actual far B copy followed by paid RIGHT8. The two branch rows remain
distinct; the caller receives nine physical FALSE cells to its WEST. -/
theorem body_bounded (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<ReturnFarActual.product risk depth y) :
    BoundedRun (bodyCode (ReturnFarActual.branch risk depth y))
      (ReturnActual.finalTape risk depth y left right) 2620 (finalTape risk depth y left) (fee risk depth y left) := by
  have copied:=ReturnDestination.bounded (ReturnFarActual.branch risk depth y) (FactorSource.factorValue risk depth : Rat) y
    (ReturnFarActual.product risk depth y) (Nat.cast_nonneg _) (le_of_lt positive)
    left (ReturnBank.bArchive risk depth) (FactorSource.bDigits risk depth)
  rw [←ReturnFarActual.actual_input risk depth y left right] at copied
  have headroom:=ReturnHeadroom.bounded (archive risk depth y left) (FactorSource.bDigits risk depth)
  have actual:=copied.seq headroom
  have port : PSTRTMSeq005.rightLabel (a:=2380) (239 : Fin 240)=(2620 : Fin 2621) := by decide
  rw [port] at actual
  simpa only [bodyCode,finalTape] using actual.mono (b:=fee risk depth y left)
    (by dsimp only [fee,ReturnFarActual.fee];omega)

theorem actual_run (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<ReturnFarActual.product risk depth y) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨entry (ReturnFarActual.branch risk depth y),ReturnActual.finalTape risk depth y left right⟩ trace
      ⟨exitPort (ReturnFarActual.branch risk depth y),finalTape risk depth y left⟩ ∧ trace.length≤fee risk depth y left := by
  obtain ⟨part,run,time⟩:=body_bounded risk depth y left right positive
  cases found : ReturnFarActual.branch risk depth y with
  | false=>
    have atRow : PSTRTMSeq005.RunsFrom (rows (0 : Fin 2))
        ⟨0,ReturnActual.finalTape risk depth y left right⟩ part ⟨2620,finalTape risk depth y left⟩ := by
      simpa only [found,rows,show ((0 : Fin 2).val==1)=false by decide] using run
    have lifted:=block_runsFrom rows ports (0 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (0 : Fin 2)),?_,?_⟩
    · exact lifted
    · rw [List.length_map]
      exact time
  | true=>
    have atRow : PSTRTMSeq005.RunsFrom (rows (1 : Fin 2))
        ⟨0,ReturnActual.finalTape risk depth y left right⟩ part ⟨2620,finalTape risk depth y left⟩ := by
      simpa only [found,rows,show ((1 : Fin 2).val==1)=true by decide] using run
    have lifted:=block_runsFrom rows ports (1 : Fin 2) _ _ part atRow (by rfl)
    refine ⟨part.map (liftCfg (1 : Fin 2)),?_,?_⟩
    · exact lifted
    · rw [List.length_map]
      exact time

theorem actual_contract (risk : Rat) (depth : ℕ) (y : Rat) (left right : ℕ)
    (positive : 0<ReturnFarActual.product risk depth y) :
    ∃ trace, PSTRTMSeq005.RunsFrom code
      ⟨entry (ReturnFarActual.branch risk depth y),ReturnActual.finalTape risk depth y left right⟩ trace
      ⟨exitPort (ReturnFarActual.branch risk depth y),finalTape risk depth y left⟩ ∧
      trace.length≤fee risk depth y left ∧
      ∀ chargedLength clock, visitedSpace code chargedLength (trace.take clock)≤chargedLength+2*fee risk depth y left+1 := by
  obtain ⟨trace,run,time⟩:=actual_run risk depth y left right positive
  refine ⟨trace,run,time,?_⟩
  intro chargedLength clock
  have space:=PSTRTMTrace002.visitedSpace_le code chargedLength (trace.take clock)
  have taken : (trace.take clock).length≤trace.length := by rw [List.length_take];exact Nat.min_le_right _ _
  omega

end RootB23.Threshold.ReturnReady
