module
public import Common.PSTR_TM_PackFrameCode_146

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRepairFrame147
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMOverlap132

def repairInitial (left remaining : List Bool) : MachineState 193 :=
  state 0 left (true::false::PSTRTMIncrement009.blocks remaining)

def repairFinal (left remaining : List Bool) : MachineState 193 :=
  state 0 left (false::false::true::false::PSTRTMIncrement009.blocks remaining)

def repairPrefix (left remaining : List Bool) : List (MachineState 193) :=
  [repairInitial left remaining,
    state 2 (true::left) (false::PSTRTMIncrement009.blocks remaining),
    liftPad (PSTRTMPackRightPadCode144.state 0 left (true::false::PSTRTMIncrement009.blocks remaining))]

theorem prefix_chain (left remaining : List Bool) :
    (repairPrefix left remaining).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) := by
  simp [repairPrefix,repairInitial,List.isChain_cons_cons,Turing.TM0.step,
    PSTRTMPackFrameCode146.packMachine,PSTRTMPackCode036.packMachine,state,liftPad,embedPad,
    PSTRTMPackRightPadCode144.state,Turing.Tape.mk₂]

def paddedTrace (left remaining : List Bool) : List (MachineState 193) :=
  (PSTRTMPackRightPadRun145.padTrace left remaining).map liftPad

def paddedInitial (left remaining : List Bool) : MachineState 193 :=
  liftPad (PSTRTMPackRightPadCode144.state 0 left (true::false::PSTRTMIncrement009.blocks remaining))

def paddedFinal (left remaining : List Bool) : MachineState 193 :=
  liftPad (PSTRTMPackRightPadCode144.state 40 left (false::false::true::false::PSTRTMIncrement009.blocks remaining))

theorem padded_head (left remaining : List Bool) :
    (paddedTrace left remaining).head?=some (paddedInitial left remaining) := by
  have hh := (PSTRTMPackRightPadRun145.pad_runsFrom left remaining).1
  simp only [paddedTrace,List.head?_map,hh,Option.map_some,paddedInitial]

theorem padded_last (left remaining : List Bool) :
    (paddedTrace left remaining).getLast?=some (paddedFinal left remaining) := by
  have hl := (PSTRTMPackRightPadRun145.pad_runsFrom left remaining).2.2.1
  simp only [paddedTrace,List.getLast?_map,hl,Option.map_some,paddedFinal]

theorem padded_chain (left remaining : List Bool) :
    (paddedTrace left remaining).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) :=
  PSTRTMPackFrameCode146.pad_chain _ (PSTRTMPackRightPadRun145.pad_runsFrom left remaining).2.1

def activeTrace (left remaining : List Bool) : List (MachineState 193) :=
  glue (repairPrefix left remaining) (paddedTrace left remaining)

theorem active_head (left remaining : List Bool) :
    (activeTrace left remaining).head?=some (repairInitial left remaining) :=
  glue_head _ _ _ _ rfl rfl (padded_head _ _)

theorem active_last (left remaining : List Bool) :
    (activeTrace left remaining).getLast?=some (paddedFinal left remaining) :=
  glue_last _ _ _ (padded_last _ _)

theorem active_chain (left remaining : List Bool) :
    (activeTrace left remaining).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) :=
  glue_chain PSTRTMPackFrameCode146.packMachine _ _ _ (prefix_chain _ _) (padded_chain _ _) rfl (padded_head _ _)

def transferTrace (left remaining : List Bool) : List (MachineState 193) :=
  [paddedFinal left remaining,repairFinal left remaining]

theorem transfer_chain (left remaining : List Bool) :
    (transferTrace left remaining).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) := by
  simp only [transferTrace,List.isChain_cons_cons,List.isChain_singleton,and_true]
  exact PSTRTMPackFrameCode146.pad_transfer _ _

/-- The actual q0/q2 dispatch, whole right insertion, and real185→0
head-preserving transfer. The final q0 is a continuation, NOT a halt or
an uncharged cursor reset. Arbitrary left data remain physically intact. -/
def repairTrace (left remaining : List Bool) : List (MachineState 193) :=
  glue (activeTrace left remaining) (transferTrace left remaining)

theorem repair_head (left remaining : List Bool) :
    (repairTrace left remaining).head?=some (repairInitial left remaining) :=
  glue_head _ _ _ _ (active_head _ _) (active_last _ _) rfl

theorem repair_last (left remaining : List Bool) :
    (repairTrace left remaining).getLast?=some (repairFinal left remaining) := glue_last _ _ _ rfl

theorem repair_chain (left remaining : List Bool) :
    (repairTrace left remaining).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) :=
  glue_chain PSTRTMPackFrameCode146.packMachine _ _ _ (active_chain _ _) (transfer_chain _ _) (active_last _ _) rfl

theorem repair_length (left remaining : List Bool) :
    (repairTrace left remaining).length=12*remaining.length+20 := by
  simp only [repairTrace,activeTrace,glue_length,repairPrefix,transferTrace,
    List.length_cons,List.length_nil,paddedTrace,List.length_map,PSTRTMPackRightPadRun145.pad_length]
  omega

theorem repair_final_tape (left remaining : List Bool) :
    (repairFinal left remaining).Tape=Turing.Tape.mk₂ left
      (false::false::true::false::PSTRTMIncrement009.blocks remaining) := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRepairFrame147
