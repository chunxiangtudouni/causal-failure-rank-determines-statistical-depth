module
public import Structure.PA17_TM_RatArithmetic_Bookmark_014b

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
open PA17TMDivisionCompose006 PA17TMRatArithmeticParse002 PA17TMRatArithmeticFieldNav012

/-- A proof wrapper around an exhibited segment of the SAME fixed code. -/
structure Piece (first last : MachineState 2303) where
  trace : List (MachineState 2303)
  run : Segment bookmarkMachine first trace last

def Piece.join {first middle next last : MachineState 2303}
    (before : Piece first middle) (after : Piece next last)
    (transfer : Turing.TM0.step bookmarkMachine middle=some next) : Piece first last where
  trace := before.trace++after.trace
  run := segment_append bookmarkMachine first middle next last before.trace after.trace before.run after.run transfer

def Piece.retarget {first last first' last' : MachineState 2303}
    (piece : Piece first last) (hi : first=first') (hf : last=last') : Piece first' last' := by
  cases hi
  cases hf
  exact piece

theorem Piece.retarget_trace {first last first' last' : MachineState 2303}
    (piece : Piece first last) (hi : first=first') (hf : last=last') :
    (piece.retarget hi hf).trace=piece.trace := by
  cases hi
  cases hf
  rfl

theorem Piece.join_length {first middle next last : MachineState 2303}
    (before : Piece first middle) (after : Piece next last)
    (transfer : Turing.TM0.step bookmarkMachine middle=some next) :
    (before.join after transfer).trace.length=before.trace.length+after.trace.length := by
  change (before.trace++after.trace).length=_
  rw [List.length_append]

theorem pad_zero {a s : Nat} (h : a≤s) (tape : Turing.Tape Bool) :
    padCfg h (⟨0,tape⟩ : MachineState a)=(⟨0,tape⟩ : MachineState s) := by
  simp only [padCfg,padLabel,Fin.val_zero,Fin.mk_zero]

def localPiece (stage : Fin 12) (memory : Fin 32) (first last : MachineState 5)
    (trace : List (MachineState 5)) (run : PSTRTMSeq005.RunsFrom (stageMachine stage) first trace last) :
    Piece (memoryCfg stage memory first) (memoryCfg stage memory last) where
  trace := trace.map (blockCfg (memoryPhase stage memory))
  run := by
    have h : PSTRTMSeq005.RunsFrom (family (memoryPhase stage memory)) first trace last := by
      rw [family_memoryPhase]
      exact run
    exact block_segment family ports (memoryPhase stage memory) first last trace h

theorem quiet_transfer (stage : Fin 12) (memory : Fin 32) (last : MachineState 5)
    (hnext : stage.val<11) (hnr : ¬IsRead stage) (halt : Turing.TM0.step (stageMachine stage) last=none) :
    Turing.TM0.step bookmarkMachine (memoryCfg stage memory last)=
      some (memoryCfg (nextStage stage hnext) memory ⟨0,last.Tape⟩) := by
  have hh : Turing.TM0.step (family (memoryPhase stage memory)) last=none := by
    rw [family_memoryPhase]
    exact halt
  apply block_transfer family ports (memoryPhase stage memory) last
    (memoryPhase (nextStage stage hnext) memory,0) hh
  simp [ports,stageOf_memoryPhase,memoryOf_memoryPhase,hnext,hnr]

def markerPiece (memory : Fin 32) (archive : List Bool) :
    Piece (memoryCfg 0 memory (padCfg (by decide : 4≤5) (markerState 0 archive [true])))
      (memoryCfg 0 memory (padCfg (by decide : 4≤5) (markerState 4 archive [false,true]))) :=
  localPiece 0 memory _ _ _ (pad_runsFrom (by decide : 4≤5) markerMachine _ _ _ (marker_runsFrom archive))

def IsBack (stage : Fin 12) : Prop := stage.val=1 ∨ stage.val=3 ∨ stage.val=7 ∨ stage.val=9
theorem stage_back (stage : Fin 12) (hb : IsBack stage) : stageMachine stage=fieldBackMachine := by
  fin_cases stage <;> simp_all [IsBack,stageMachine] <;> rfl

def backPiece (stage : Fin 12) (memory : Fin 32) (archive digits suffix : List Bool) (hb : IsBack stage) :
    Piece (memoryCfg stage memory ⟨0,Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) suffix⟩)
      (memoryCfg stage memory (fieldBackFinal archive digits suffix)) :=
  localPiece stage memory
    ⟨0,Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks digits.reverse++false::archive)) suffix⟩
    (fieldBackFinal archive digits suffix) (fieldBackTrace archive digits suffix)
    (by rw [stage_back stage hb];exact fieldBack_runsFrom archive digits suffix)

def headerPiece (memory : Fin 32) (archive : List Bool) (near far : Bool) (suffix : List Bool) :
    Piece (memoryCfg 5 memory (padCfg (by decide : 2≤5) (headerState 0 (near::far::archive) suffix)))
      (memoryCfg 5 memory (padCfg (by decide : 2≤5) (headerState 2 archive (far::near::suffix)))) :=
  localPiece 5 memory _ _ _ (pad_runsFrom (by decide : 2≤5) headerBackMachine _ _ _
    (headerBack_runsFrom archive near far suffix))

def readEnd (bit : Bool) (tape : Turing.Tape Bool) : MachineState 5 :=
  padCfg (by decide : 2≤5) ⟨readPort bit,tape⟩

def readPiece (stage : Fin 12) (memory : Fin 32) (archive : List Bool) (bit : Bool) (suffix : List Bool)
    (hr : IsRead stage) :
    Piece (memoryCfg stage memory ⟨0,Turing.Tape.mk₂ archive (bit::suffix)⟩)
      (memoryCfg stage memory (readEnd bit (Turing.Tape.mk₂ archive (false::suffix)))) where
  trace := readBlockTrace stage memory archive bit suffix
  run := by
    simpa only [readState,pad_zero,readEnd] using read_block_segment stage memory archive bit suffix hr

theorem read_transfer (stage : Fin 12) (memory : Fin 32) (archive : List Bool) (bit : Bool) (suffix : List Bool)
    (hr : IsRead stage) (hnext : stage.val<11) :
    Turing.TM0.step bookmarkMachine (memoryCfg stage memory (readEnd bit (Turing.Tape.mk₂ archive (false::suffix))))=
      some (memoryCfg (nextStage stage hnext) (saveBit memory (readWeight stage) bit)
        ⟨0,Turing.Tape.mk₂ archive (false::suffix)⟩) := by
  simpa only [readState,readEnd] using read_block_transfer stage memory archive bit suffix hr hnext

def fieldReadPiece (stage : Fin 12) (memory : Fin 32) (archive digits suffix : List Bool)
    (hne : digits≠[]) (hr : IsRead stage) :
    Piece (memoryCfg stage memory ⟨0,Turing.Tape.mk₂ archive (PSTRTMIncrement009.blocks digits++suffix)⟩)
      (memoryCfg stage memory (readEnd (observedFirst digits)
        (Turing.Tape.mk₂ archive (PSTRTMIncrement009.blocks (clampFirst digits)++suffix)))) :=
  (readPiece stage memory archive (observedFirst digits)
    (true::(PSTRTMIncrement009.blocks digits.tail++suffix)) hr).retarget
    (by rw [blocks_observedFirst digits hne];simp only [List.cons_append])
    (by rw [blocks_clampFirst];simp only [List.cons_append])

theorem field_read_transfer (stage : Fin 12) (memory : Fin 32) (archive digits suffix : List Bool)
    (hr : IsRead stage) (hnext : stage.val<11) :
    Turing.TM0.step bookmarkMachine
      (memoryCfg stage memory (readEnd (observedFirst digits)
        (Turing.Tape.mk₂ archive (PSTRTMIncrement009.blocks (clampFirst digits)++suffix))))=
      some (memoryCfg (nextStage stage hnext) (saveBit memory (readWeight stage) (observedFirst digits))
        ⟨0,Turing.Tape.mk₂ archive (PSTRTMIncrement009.blocks (clampFirst digits)++suffix)⟩) := by
  simpa only [blocks_clampFirst,List.cons_append] using read_transfer stage memory archive
    (observedFirst digits) (true::(PSTRTMIncrement009.blocks digits.tail++suffix)) hr hnext

def donePiece (memory : Fin 32) (tape : Turing.Tape Bool) :
    Piece (memoryCfg 11 memory ⟨0,tape⟩) (memoryCfg 11 memory ⟨0,tape⟩) where
  trace := [memoryCfg 11 memory ⟨0,tape⟩]
  run := ⟨rfl,by simp,rfl⟩

theorem done_halt (memory : Fin 32) (tape : Turing.Tape Bool) :
    Turing.TM0.step bookmarkMachine (memoryCfg 11 memory ⟨0,tape⟩)=none := by
  apply block_halt family ports (memoryPhase 11 memory) ⟨0,tape⟩
  · rw [family_memoryPhase]
    rfl
  · simp [ports,stageOf_memoryPhase]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticBookmark014
