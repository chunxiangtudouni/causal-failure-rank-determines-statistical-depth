module
public import Structure.PA17_TM_Division_Codec_003e
public import Common.PSTR_TM_CompareRun_059

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
open PaperProofs.Common.Native.RationalControllerComputation

theorem leftColumns_reverse_columns (pairs : List (Bool × Bool)) :
    PSTRTMCompareCode054.leftColumns pairs.reverse =
      (PSTRTMBinaryAdd024.operandColumns pairs).reverse := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
      obtain ⟨a,b⟩ := pair
      simpa only [List.reverse_cons, PSTRTMCompareCode054.leftColumns, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.cons_append, List.nil_append,
        PSTRTMBinaryAdd024.operandColumns, List.reverse_append, List.reverse_cons,
        List.reverse_nil, List.append_nil, List.append_assoc] using
        congrArg (fun word => word ++ [true,b,true,a]) ih

def backThreeMachine : Machine 3 := fun q _ =>
  if h : q.val < 3 then some (⟨q.val + 1, by omega⟩, .move .left) else none

def backThreeState (q : Fin 4) (left right : List Bool) : MachineState 3 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def backThreeTrace (left right : List Bool) : List (MachineState 3) :=
  [backThreeState 0 (false :: false :: false :: left) right,
   backThreeState 1 (false :: false :: left) (false :: right),
   backThreeState 2 (false :: left) (false :: false :: right),
   backThreeState 3 left (false :: false :: false :: right)]

theorem backThree_runsFrom (left right : List Bool) :
    PSTRTMSeq005.RunsFrom backThreeMachine
      (backThreeState 0 (false :: false :: false :: left) right)
      (backThreeTrace left right)
      (backThreeState 3 left (false :: false :: false :: right)) := by
  refine ⟨rfl, ?_, rfl, ?_⟩
  · simp [backThreeTrace, List.isChain_cons_cons, Turing.TM0.step,
      backThreeMachine, backThreeState, Turing.Tape.mk₂]
  · simp [Turing.TM0.step, backThreeMachine, backThreeState]

/-- All three real separator cells are crossed before frozen067 rewinds
the archive's actual column flags. Neither operation resets the tape. -/
def returnArchiveMachine : Machine 9 :=
  PSTRTMSeq005.seqMachine backThreeMachine PSTRTMColumnRewind067.rewindMachine

def returnArchiveInitial (pairs : List (Bool × Bool)) (tail : List Bool) : MachineState 9 :=
  ⟨0, Turing.Tape.mk₂
    (false :: false :: false :: (PSTRTMCompareCode054.leftColumns pairs.reverse ++ [false])) tail⟩

def returnArchiveTrace (pairs : List (Bool × Bool)) (tail : List Bool) : List (MachineState 9) :=
  (backThreeTrace (PSTRTMCompareCode054.leftColumns pairs.reverse ++ [false]) tail).map
      (PSTRTMSeq005.leftCfg (b := 5)) ++
    (PSTRTMColumnRewind067.fullTrace [] pairs.reverse (false :: false :: false :: tail)).map
      (PSTRTMSeq005.rightCfg (a := 3))

def returnArchiveFinal (pairs : List (Bool × Bool)) (tail : List Bool) : MachineState 9 :=
  PSTRTMSeq005.rightCfg (a := 3)
    (PSTRTMColumnRewind067.state 5 [false]
      (PSTRTMBinaryAdd024.operandColumns pairs ++ false :: false :: false :: tail))

theorem returnArchive_runsFrom (pairs : List (Bool × Bool)) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom returnArchiveMachine (returnArchiveInitial pairs tail)
      (returnArchiveTrace pairs tail) (returnArchiveFinal pairs tail) := by
  apply PSTRTMSeq005.seq_runsFrom backThreeMachine PSTRTMColumnRewind067.rewindMachine
    _ _ _ _ _ (backThree_runsFrom _ _)
  exact PSTRTMColumnRewind067.rewind_runsFrom [] pairs (false :: false :: false :: tail)

theorem returnArchive_final_tape (pairs : List (Bool × Bool)) :
    (returnArchiveFinal pairs []).Tape = Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns pairs) := by
  simp only [returnArchiveFinal, PSTRTMSeq005.rightCfg, PSTRTMColumnRewind067.state,
    Turing.Tape.mk₁, Turing.Tape.mk₂]
  rw [PSTRTMRawNat010.blank_single_false]
  have hb : Turing.ListBlank.mk (PSTRTMBinaryAdd024.operandColumns pairs ++ [false,false,false]) =
      Turing.ListBlank.mk (PSTRTMBinaryAdd024.operandColumns pairs) :=
    PSTRTMPackFinish039.blank_false_suffix (PSTRTMBinaryAdd024.operandColumns pairs) 3
  rw [hb]

theorem returnArchiveTrace_length (pairs : List (Bool × Bool)) (tail : List Bool) :
    (returnArchiveTrace pairs tail).length = 4 * pairs.length + 7 := by
  simp only [returnArchiveTrace, List.length_append, List.length_map, backThreeTrace,
    List.length_cons, List.length_nil, PSTRTMColumnRewind067.full_length, List.length_reverse]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCodec003
