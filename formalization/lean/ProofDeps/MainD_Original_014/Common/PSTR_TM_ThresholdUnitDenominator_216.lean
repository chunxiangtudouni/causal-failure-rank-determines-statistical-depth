module
public import Common.PSTR_TM_ThresholdOddsNatCost_210

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitDenominator216
open PaperProofs.Common.Native.RationalControllerComputation

/-! Threshold-specific literal denominator preparation on genuinely blank
RIGHT. It finds the flagged field's actual OWN00, writes the fixed suffix
FALSE TRUE beyond those TWO cells, and really returns to the first digit.
The frozen marker inverse004d can then produce rawNat(n) ++ encodeNat(1).
No arbitrary suffix, supplied width or unallocated window is assumed. -/

def plantMachine : Machine 8 := fun q symbol =>
  match q.val with
  | 0 => some (1,.move .right)
  | 1 => some (if symbol then 0 else 2,.move .right)
  | 2 => some (3,.write false)
  | 3 => some (4,.move .right)
  | 4 => some (5,.write true)
  | 5 => some (6,.move .left)
  | 6 => some (7,.move .left)
  | 7 => some (8,.move .left)
  | _ => none

def state (q : Fin 9) (left right : List Bool) : MachineState 8 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def endLeft (left digits : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks digits.reverse ++ left

def scanTrace (left : List Bool) : List Bool → List (MachineState 8)
  | [] => [state 0 left [],state 1 (false::left) []]
  | bit::later =>
    [state 0 left (bit::true::PSTRTMIncrement009.blocks later),
     state 1 (bit::left) (true::PSTRTMIncrement009.blocks later)] ++
      scanTrace (true::bit::left) later

def plantFinish (left : List Bool) : List (MachineState 8) :=
  [state 2 (false::false::left) [],
   state 3 (false::false::left) [],
   state 4 (false::false::false::left) [],
   state 5 (false::false::false::left) [true],
   state 6 (false::false::left) [false,true],
   state 7 (false::left) [false,false,true],
   state 8 left [false,false,false,true]]

def plantTrace (left digits : List Bool) : List (MachineState 8) :=
  scanTrace left digits ++ plantFinish (endLeft left digits)

def plantFinal (left digits : List Bool) : MachineState 8 :=
  state 8 (endLeft left digits) [false,false,false,true]

theorem scan_head (left digits : List Bool) :
    (scanTrace left digits).head? = some (state 0 left (PSTRTMIncrement009.blocks digits)) := by
  cases digits <;> rfl

theorem scan_last (left digits : List Bool) :
    (scanTrace left digits).getLast? = some (state 1 (false::endLeft left digits) []) := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    have hne : scanTrace (true::bit::left) later ≠ [] := by
      intro he
      have hh := scan_head (true::bit::left) later
      simp [he] at hh
    simp only [scanTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [endLeft,PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem scan_length (left digits : List Bool) : (scanTrace left digits).length = 2*digits.length+2 := by
  induction digits generalizing left with
  | nil => rfl
  | cons bit later ih =>
    simp only [scanTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem scan_chain (left digits : List Bool) :
    (scanTrace left digits).IsChain (fun before after => Turing.TM0.step plantMachine before = some after) := by
  induction digits generalizing left with
  | nil => simp [scanTrace,List.isChain_cons_cons,Turing.TM0.step,plantMachine,state,Turing.Tape.mk₂]
  | cons bit later ih =>
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,plantMachine,state,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [scan_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,plantMachine,state,Turing.Tape.mk₂]

theorem plant_runsFrom (left digits : List Bool) :
    PSTRTMSeq005.RunsFrom plantMachine
      (state 0 left (PSTRTMIncrement009.blocks digits)) (plantTrace left digits) (plantFinal left digits) := by
  refine ⟨?_,?_,?_,?_⟩
  · simp only [plantTrace,List.head?_append,scan_head,Option.some_or]
  · apply (scan_chain left digits).append
    · simp [plantFinish,List.isChain_cons_cons,Turing.TM0.step,plantMachine,state,Turing.Tape.mk₂,
        PSTRTMRawNat010.blank_single_false]
    · intro before hb after ha
      simp only [scan_last,Option.mem_some_iff] at hb
      simp only [plantFinish,List.head?_cons,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,plantMachine,state,Turing.Tape.mk₂]
  · simp [plantTrace,plantFinish,plantFinal]
  · simp [plantFinal,Turing.TM0.step,plantMachine,state]

theorem plant_length (left digits : List Bool) : (plantTrace left digits).length = 2*digits.length+9 := by
  simp only [plantTrace,List.length_append,scan_length,plantFinish,List.length_cons,List.length_nil]

/-- Fixed13 labels: the literal suffix writes plus the SAME frozen4-label
pair rewind105. The real false left guard and all external archive survive. -/
def prepareMachine : Machine 12 :=
  PSTRTMSeq005.seqMachine plantMachine PSTRTMMulRewind085.rewindMachine

def prepareTrace (archive digits : List Bool) : List (MachineState 12) :=
  (plantTrace (false::archive) digits).map (PSTRTMSeq005.leftCfg (b := 3)) ++
  (PSTRTMPairRewind105.fullTrace archive digits.reverse [false,false,false,true]).map
    (PSTRTMSeq005.rightCfg (a := 8))

def prepareFinal (archive digits : List Bool) : MachineState 12 :=
  PSTRTMSeq005.rightCfg (a := 8) (PSTRTMMulRewind085.state 3 (false::archive)
    (PSTRTMIncrement009.blocks digits ++ [false,false,false,true]))

theorem prepare_runsFrom (archive digits : List Bool) :
    PSTRTMSeq005.RunsFrom prepareMachine
      ⟨0,Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits)⟩
      (prepareTrace archive digits) (prepareFinal archive digits) := by
  apply PSTRTMSeq005.seq_runsFrom plantMachine PSTRTMMulRewind085.rewindMachine
    (state 0 (false::archive) (PSTRTMIncrement009.blocks digits)) (plantFinal (false::archive) digits)
    (PSTRTMMulRewind085.state 3 (false::archive)
      (PSTRTMIncrement009.blocks digits ++ [false,false,false,true]))
    (plantTrace (false::archive) digits)
    (PSTRTMPairRewind105.fullTrace archive digits.reverse [false,false,false,true])
    (plant_runsFrom _ _)
  exact PSTRTMPairRewind105.rewind_runsFrom archive digits [false,false,false,true]

theorem prepare_final_tape (archive digits : List Bool) :
    (prepareFinal archive digits).Tape = Turing.Tape.mk₂ (false::archive)
      (PSTRTMIncrement009.blocks digits ++ false::false::[false,true]) := rfl

theorem prepare_length (archive digits : List Bool) :
    (prepareTrace archive digits).length = 4*digits.length+12 := by
  simp only [prepareTrace,List.length_append,List.length_map,plant_length,
    PSTRTMPairRewind105.full_length,List.length_reverse]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdUnitDenominator216
