module

public import Common.PSTR_TM_Seq_005
public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.BoolCompose

open PaperProofs.Paid.Computation

variable {a b c : ℕ}

/-- The existing finite table performs a real write-self at the first
HALT. The second table starts at zero on that SAME entire Tape/head. -/
abbrev machine (first : BitMachine a) (second : BitMachine b) : BitMachine (a+b+1) :=
  PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.seqMachine first second

abbrev trace (first : List (BitState a)) (second : List (BitState b)) :
    List (BitState (a+b+1)) :=
  first.map (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.leftCfg (b:=b)) ++ second.map (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a))

theorem segment_of_bit_runs (code : BitMachine a) (input : List Bool)
    (states : List (BitState a)) (final : BitState a) (actual : BitRuns code input states final) :
    PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom code (Turing.TM0.init input) states final :=
  ⟨actual.1,actual.2.1,actual.2.2.1,actual.2.2.2.1⟩

/-- Only an equality of the WHOLE Tape supplies this entry. Equality of
right-zero output alone never resets an old left archive or its cursor. -/
theorem segment_on_actual_tape (code : BitMachine a) (input : List Bool)
    (tape : Turing.Tape Bool) (states : List (BitState a)) (final : BitState a)
    (whole : tape=Turing.Tape.mk₁ input) (actual : BitRuns code input states final) :
    PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom code ⟨0,tape⟩ states final := by
  subst tape
  exact segment_of_bit_runs code input states final actual

theorem actual_segment (first : BitMachine a) (second : BitMachine b)
    (initial finalFirst : BitState a) (finalSecond : BitState b)
    (statesFirst : List (BitState a)) (statesSecond : List (BitState b))
    (left : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom first initial statesFirst finalFirst)
    (right : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom second ⟨0,finalFirst.Tape⟩ statesSecond finalSecond) :
    PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom (machine first second) (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.leftCfg (b:=b) initial)
      (trace statesFirst statesSecond) (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a) finalSecond) :=
  PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.seq_runsFrom first second initial finalFirst finalSecond statesFirst statesSecond left right

theorem actual_run (first : BitMachine a) (second : BitMachine b) (input : List Bool)
    (finalFirst : BitState a) (finalSecond : BitState b)
    (statesFirst : List (BitState a)) (statesSecond : List (BitState b))
    (left : BitRuns first input statesFirst finalFirst)
    (right : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom second ⟨0,finalFirst.Tape⟩ statesSecond finalSecond) :
    BitRuns (machine first second) input (trace statesFirst statesSecond)
      (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a) finalSecond) := by
  have firstActual : PaperProofs.Common.Native.RationalControllerComputation.Runs first input statesFirst finalFirst := left
  exact PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.seq_runs first second input finalFirst finalSecond statesFirst statesSecond firstActual right

theorem trace_length (statesFirst : List (BitState a)) (statesSecond : List (BitState b)) :
    (trace statesFirst statesSecond).length=statesFirst.length+statesSecond.length :=
  PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.seq_trace_length statesFirst statesSecond

theorem final_tape (final : BitState b) :
    (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a) final).Tape=final.Tape := rfl

theorem actual_three_run (first : BitMachine a) (second : BitMachine b) (third : BitMachine c)
    (input : List Bool) (finalFirst : BitState a) (finalSecond : BitState b) (finalThird : BitState c)
    (statesFirst : List (BitState a)) (statesSecond : List (BitState b)) (statesThird : List (BitState c))
    (left : BitRuns first input statesFirst finalFirst)
    (middle : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom second ⟨0,finalFirst.Tape⟩ statesSecond finalSecond)
    (right : PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.RunsFrom third ⟨0,finalSecond.Tape⟩ statesThird finalThird) :
    BitRuns (machine (machine first second) third) input
      (trace (trace statesFirst statesSecond) statesThird)
      (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a+b+1) finalThird) := by
  have actualFirstTwo := actual_run first second input finalFirst finalSecond statesFirst statesSecond left middle
  exact actual_run (machine first second) third input (PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005.rightCfg (a:=a) finalSecond) finalThird
    (trace statesFirst statesSecond) statesThird actualFirstTwo right

end PDROC.BitVM.VM.BoolCompose
