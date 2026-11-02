module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018

/-- Observe DATA and carry it in a finite HALT label; the DATA is never written. -/
def readDataMachine : Machine 2 := fun q symbol =>
  if q.val=0 then some (PA17TMRatArithmeticBookmark014.readPort symbol,.move .right) else none

def readDataTrace (left : List Bool) (data flag : Bool) (suffix : List Bool) : List (MachineState 2) :=
  [markState 0 left (data::flag::suffix),
   markState (PA17TMRatArithmeticBookmark014.readPort data) (data::left) (flag::suffix)]

theorem readData_runsFrom (left : List Bool) (data flag : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom readDataMachine (markState 0 left (data::flag::suffix))
      (readDataTrace left data flag suffix)
      (markState (PA17TMRatArithmeticBookmark014.readPort data) (data::left) (flag::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · cases data <;> simp [readDataTrace,List.isChain_cons_cons,Turing.TM0.step,readDataMachine,
      markState,PA17TMRatArithmeticBookmark014.readPort,Turing.Tape.mk₂]
  · cases data <;> simp [Turing.TM0.step,readDataMachine,markState,PA17TMRatArithmeticBookmark014.readPort]

def readMarkRows (phase : Fin 3) : Machine 2 := if phase.val=0 then readDataMachine else markMachine

def readMarkPorts (phase localLabel : Fin 3) : Option (Fin 3 × Fin 3) :=
  if phase.val=0 ∧ localLabel.val≠0 then some (localLabel,0) else none

def readMarkMachine : Machine 8 := blockMachine readMarkRows readMarkPorts

def readMarkFirst (left : List Bool) (bit flag : Bool) (suffix : List Bool) : MachineState 8 :=
  blockCfg (0 : Fin 3) (markState 0 left (bit::flag::suffix))

def readMarkLast (left : List Bool) (bit : Bool) (suffix : List Bool) : MachineState 8 :=
  blockCfg (PA17TMRatArithmeticBookmark014.readPort bit) (markState 2 (false::bit::left) suffix)

def readMarkTrace (left : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 8) :=
  (readDataTrace left bit true suffix).map (blockCfg (0 : Fin 3)) ++
  (markTrace (bit::left) suffix).map (blockCfg (PA17TMRatArithmeticBookmark014.readPort bit))

/-- Read DATA, actually clear its TRUE flag, and advance to NEXT DATA.
The observed DATA is retained both on tape and in the actual final phase. -/
theorem readMark_runsFrom (left : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom readMarkMachine (readMarkFirst left bit true suffix)
      (readMarkTrace left bit suffix) (readMarkLast left bit suffix) := by
  have hr : PSTRTMSeq005.RunsFrom (readMarkRows 0) (markState 0 left (bit::true::suffix))
      (readDataTrace left bit true suffix)
      (markState (PA17TMRatArithmeticBookmark014.readPort bit) (bit::left) (true::suffix)) :=
    readData_runsFrom left bit true suffix
  have hm : PSTRTMSeq005.RunsFrom (readMarkRows (PA17TMRatArithmeticBookmark014.readPort bit))
      (markState 0 (bit::left) (true::suffix)) (markTrace (bit::left) suffix)
      (markState 2 (false::bit::left) suffix) := by
    cases bit <;> exact mark_runsFrom _ _
  have hs := segment_append readMarkMachine _ _ _ _ _ _
    (block_segment readMarkRows readMarkPorts 0 _ _ _ hr)
    (block_segment readMarkRows readMarkPorts (PA17TMRatArithmeticBookmark014.readPort bit) _ _ _ hm)
    (block_transfer readMarkRows readMarkPorts 0 _ (PA17TMRatArithmeticBookmark014.readPort bit,0)
      hr.2.2.2 (by cases bit <;> rfl))
  exact segment_runsFrom _ _ _ _ hs
    (block_halt readMarkRows readMarkPorts (PA17TMRatArithmeticBookmark014.readPort bit) _ hm.2.2.2
      (by cases bit <;> rfl))

theorem readMarkTrace_length (left : List Bool) (bit : Bool) (suffix : List Bool) :
    (readMarkTrace left bit suffix).length=5 := rfl

theorem readMark_saved_bit (left : List Bool) (bit : Bool) (suffix : List Bool) :
    phaseOf (p:=2) (s:=2) (readMarkLast left bit suffix).q=PA17TMRatArithmeticBookmark014.readPort bit :=
  phaseOf_label _ _

def eofTrace (left suffix : List Bool) : List (MachineState 8) :=
  (readDataTrace left false false suffix).map (blockCfg (0 : Fin 3)) ++
    [blockCfg (1 : Fin 3) (markState 0 (false::left) (false::suffix))]

/-- A real source END00 halts without clearing or advancing the local footer. -/
theorem eof_runsFrom (left suffix : List Bool) :
    PSTRTMSeq005.RunsFrom readMarkMachine (readMarkFirst left false false suffix)
      (eofTrace left suffix) (blockCfg (1 : Fin 3) (markState 0 (false::left) (false::suffix))) := by
  have hr : PSTRTMSeq005.RunsFrom (readMarkRows 0) (markState 0 left (false::false::suffix))
      (readDataTrace left false false suffix) (markState 1 (false::left) (false::suffix)) :=
    readData_runsFrom left false false suffix
  have hm : PSTRTMSeq005.RunsFrom (readMarkRows 1) (markState 0 (false::left) (false::suffix))
      [markState 0 (false::left) (false::suffix)] (markState 0 (false::left) (false::suffix)) :=
    mark_false_halt _ _
  have hs := segment_append readMarkMachine _ _ _ _ _ _
    (block_segment readMarkRows readMarkPorts 0 _ _ _ hr)
    (block_segment readMarkRows readMarkPorts 1 _ _ _ hm)
    (block_transfer readMarkRows readMarkPorts 0 _ (1,0) hr.2.2.2 rfl)
  exact segment_runsFrom _ _ _ _ hs (block_halt readMarkRows readMarkPorts 1 _ hm.2.2.2 rfl)

theorem eofTrace_length (left suffix : List Bool) : (eofTrace left suffix).length=3 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
