module
public import Structure.PA17_TM_RatArithmetic_Parse_002f
public import Common.PSTR_TM_PairRewind_105

/-! Real fixed cursor connectors. Crossing the footer makes no assertion
that an arbitrary suffix is blank. Only the original standalone input has
the proved blank workspace. Field rewind reads its genuine false guard. -/

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002

def footerMachine : Machine 1 := fun q _ =>
  if q.val=0 then some (1,.move .right) else none

def backOneMachine : Machine 1 := fun q _ =>
  if q.val=0 then some (1,.move .left) else none

def cursorState (q : Fin 2) (left right : List Bool) : MachineState 1 :=
  ⟨q,Turing.Tape.mk₂ left right⟩

def footerTrace (archive suffix : List Bool) : List (MachineState 1) :=
  [cursorState 0 archive (true::suffix),cursorState 1 (true::archive) suffix]

theorem footer_runsFrom (archive suffix : List Bool) :
    PSTRTMSeq005.RunsFrom footerMachine (cursorState 0 archive (true::suffix))
      (footerTrace archive suffix) (cursorState 1 (true::archive) suffix) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [footerTrace,List.isChain_cons_cons,Turing.TM0.step,footerMachine,cursorState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,footerMachine,cursorState]

def backOneTrace (archive : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 1) :=
  [cursorState 0 (bit::archive) suffix,cursorState 1 archive (bit::suffix)]

theorem backOne_runsFrom (archive : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom backOneMachine (cursorState 0 (bit::archive) suffix)
      (backOneTrace archive bit suffix) (cursorState 1 archive (bit::suffix)) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [backOneTrace,List.isChain_cons_cons,Turing.TM0.step,backOneMachine,cursorState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,backOneMachine,cursorState]

def fieldBackMachine : Machine 5 :=
  PSTRTMSeq005.seqMachine backOneMachine PSTRTMMulRewind085.rewindMachine

def fieldBackTrace (archive digits suffix : List Bool) : List (MachineState 5) :=
  (backOneTrace (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) false suffix).map
      (PSTRTMSeq005.leftCfg (b:=3)) ++
    (PSTRTMPairRewind105.fullTrace archive digits.reverse (false::suffix)).map
      (PSTRTMSeq005.rightCfg (a:=1))

def fieldBackFinal (archive digits suffix : List Bool) : MachineState 5 :=
  PSTRTMSeq005.rightCfg (a:=1) (PSTRTMMulRewind085.state 3 (false::archive)
    (PSTRTMIncrement009.blocks digits++false::suffix))

/-- Start immediately after a field's real right-end false cell; move
onto it and actually rewind the flagged field, preserving both sides. -/
theorem fieldBack_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom fieldBackMachine
      ⟨0,Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) suffix⟩
      (fieldBackTrace archive digits suffix) (fieldBackFinal archive digits suffix) := by
  have h := PSTRTMSeq005.seq_runsFrom backOneMachine PSTRTMMulRewind085.rewindMachine
    (cursorState 0 (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) suffix)
    (cursorState 1 (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) (false::suffix))
    (PSTRTMMulRewind085.state 3 (false::archive) (PSTRTMIncrement009.blocks digits++false::suffix))
    (backOneTrace (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) false suffix)
    (PSTRTMPairRewind105.fullTrace archive digits.reverse (false::suffix))
    (backOne_runsFrom (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) false suffix)
    (PSTRTMPairRewind105.rewind_runsFrom archive digits (false::suffix))
  simpa only [fieldBackMachine,fieldBackTrace,fieldBackFinal,cursorState,PSTRTMSeq005.leftCfg,
    PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem fieldBack_final_tape (archive digits suffix : List Bool) :
    (fieldBackFinal archive digits suffix).Tape =
      Turing.Tape.mk₂ (false::archive) (PSTRTMIncrement009.blocks digits++false::suffix) := rfl

theorem fieldBackTrace_length (archive digits suffix : List Bool) :
    (fieldBackTrace archive digits suffix).length = 2*digits.length+5 := by
  change (((backOneTrace (PSTRTMRawNat010.leftBlocks digits.reverse++false::archive) false suffix).map
        (PSTRTMSeq005.leftCfg (a:=1) (b:=3))) ++
    (PSTRTMPairRewind105.fullTrace archive digits.reverse (false::suffix)).map
      (PSTRTMSeq005.rightCfg (a:=1) (b:=3))).length = _
  rw [List.length_append,List.length_map,List.length_map,PSTRTMPairRewind105.full_length,List.length_reverse]
  change 2+(2*digits.length+3) = _
  omega

def workspaceMachine : Machine 99 := PSTRTMSeq005.seqMachine originalParserMachine footerMachine

def workspaceTrace (x y : Rat) : List (MachineState 99) :=
  (originalParserTrace x y).map (PSTRTMSeq005.leftCfg (b:=1)) ++
    (footerTrace (ratLeft (ratLeft (listPrefixLeft []) x) y) []).map (PSTRTMSeq005.rightCfg (a:=97))

def workspaceFinal (x y : Rat) : MachineState 99 :=
  PSTRTMSeq005.rightCfg (a:=97) (cursorState 1 (true::ratLeft (ratLeft (listPrefixLeft []) x) y) [])

/-- Only the original standalone pair has a blank right workspace. The
footer crossing, all original parsing and actual transfer are charged. -/
theorem workspace_runs (x y : Rat) :
    Runs workspaceMachine (encode [.rational x,.rational y]) (workspaceTrace x y) (workspaceFinal x y) :=
  PSTRTMSeq005.seq_runs originalParserMachine footerMachine (encode [.rational x,.rational y])
    (originalParserFinal x y) (cursorState 1 (true::ratLeft (ratLeft (listPrefixLeft []) x) y) [])
    (originalParserTrace x y) (footerTrace (ratLeft (ratLeft (listPrefixLeft []) x) y) [])
    (originalParser_runs x y) (footer_runsFrom (ratLeft (ratLeft (listPrefixLeft []) x) y) [])

theorem workspace_final_tape (x y : Rat) :
    (workspaceFinal x y).Tape = Turing.Tape.mk₂ (true::ratLeft (ratLeft (listPrefixLeft []) x) y) [] := rfl

theorem workspaceTrace_length (x y : Rat) :
    (workspaceTrace x y).length = (originalParserTrace x y).length+2 := by
  change (((originalParserTrace x y).map (PSTRTMSeq005.leftCfg (a:=97) (b:=1))) ++
    (footerTrace (ratLeft (ratLeft (listPrefixLeft []) x) y) []).map
      (PSTRTMSeq005.rightCfg (a:=97) (b:=1))).length = _
  rw [List.length_append,List.length_map,List.length_map]
  rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticParse002
