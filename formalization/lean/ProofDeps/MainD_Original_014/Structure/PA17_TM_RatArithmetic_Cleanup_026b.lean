module
public import Structure.PA17_TM_RatArithmetic_Cleanup_026a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCleanup026

open Turing

def clearHeaderMachine : Machine 4 := fun q _symbol =>
  match q.val with
  | 0 => some (1,.write false)
  | 1 => some (2,.move .right)
  | 2 => some (3,.write false)
  | 3 => some (4,.move .right)
  | _ => none

def clearState (q : Fin 5) (left right : List Bool) : MachineState 4 := ⟨q,Tape.mk₂ left right⟩

def clearTrace (archive word : List Bool) : List (MachineState 4) :=
  [clearState 0 archive (true::false::word),clearState 1 archive (false::false::word),
   clearState 2 (false::archive) (false::word),clearState 3 (false::archive) (false::word),
   clearState 4 (false::false::archive) word]

theorem clear_runsFrom (archive word : List Bool) :
    PSTRTMSeq005.RunsFrom clearHeaderMachine (clearState 0 archive (true::false::word))
      (clearTrace archive word) (clearState 4 (false::false::archive) word) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [clearTrace,List.isChain_cons_cons,TM0.step,clearHeaderMachine,clearState,Tape.mk₂]
  · simp [TM0.step,clearHeaderMachine,clearState]

theorem clearTrace_length (archive word : List Bool) : (clearTrace archive word).length = 5 := rfl

def advanceTrace (left : List Bool) (bit : Bool) (suffix : List Bool) : List (MachineState 1) :=
  [PA17TMRatArithmeticParse002.cursorState 0 left (bit::suffix),
   PA17TMRatArithmeticParse002.cursorState 1 (bit::left) suffix]

/-- Reuse the actual frozen RIGHT machine, proving its FALSE-head step
directly. The old footer_runsFrom only describes TRUE-head entry. -/
theorem advance_runsFrom (left : List Bool) (bit : Bool) (suffix : List Bool) :
    PSTRTMSeq005.RunsFrom PA17TMRatArithmeticParse002.footerMachine
      (PA17TMRatArithmeticParse002.cursorState 0 left (bit::suffix))
      (advanceTrace left bit suffix)
      (PA17TMRatArithmeticParse002.cursorState 1 (bit::left) suffix) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [advanceTrace,List.isChain_cons_cons,TM0.step,PA17TMRatArithmeticParse002.footerMachine,
      PA17TMRatArithmeticParse002.cursorState,Tape.mk₂]
  · simp [TM0.step,PA17TMRatArithmeticParse002.footerMachine,PA17TMRatArithmeticParse002.cursorState]

theorem advanceTrace_length (left : List Bool) (bit : Bool) (suffix : List Bool) :
    (advanceTrace left bit suffix).length = 2 := rfl

def recordWord (digits suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::false::true::suffix

def bodyMachine : Machine 8 := PSTRTMSeq005.seqMachine clearHeaderMachine fieldEraseMachine

def bodyTrace (archive digits suffix : List Bool) : List (MachineState 8) :=
  (clearTrace archive (recordWord digits suffix)).map (PSTRTMSeq005.leftCfg (b:=3)) ++
    (fieldTrace (false::false::archive) digits (true::suffix)).map (PSTRTMSeq005.rightCfg (a:=4))

def bodyFinal (archive digits suffix : List Bool) : MachineState 8 :=
  PSTRTMSeq005.rightCfg (a:=4) (fieldFinal (false::false::archive) digits (true::suffix))

theorem body_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom bodyMachine
      ⟨0,Tape.mk₂ archive (true::false::recordWord digits suffix)⟩
      (bodyTrace archive digits suffix) (bodyFinal archive digits suffix) := by
  have hr := PSTRTMSeq005.seq_runsFrom clearHeaderMachine fieldEraseMachine
    (clearState 0 archive (true::false::recordWord digits suffix))
    (clearState 4 (false::false::archive) (recordWord digits suffix))
    (fieldFinal (false::false::archive) digits (true::suffix))
    (clearTrace archive (recordWord digits suffix))
    (fieldTrace (false::false::archive) digits (true::suffix))
    (clear_runsFrom archive (recordWord digits suffix))
    (field_runsFrom (false::false::archive) digits (true::suffix))
  simpa only [bodyMachine,bodyTrace,bodyFinal,clearState,PSTRTMSeq005.leftCfg,
    PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using hr

/-- Fixed11labels, chosen before every field/archive/suffix. EndTRUE stays
TRUE; the final head gets there by an actual RIGHT across secondOWNfalse. -/
def recordEraseMachine : Machine 10 :=
  PSTRTMSeq005.seqMachine bodyMachine PA17TMRatArithmeticParse002.footerMachine

def erasedLeft (archive digits : List Bool) : List Bool :=
  List.replicate (2*digits.length+1) false++false::false::archive

def recordTrace (archive digits suffix : List Bool) : List (MachineState 10) :=
  (bodyTrace archive digits suffix).map (PSTRTMSeq005.leftCfg (b:=1)) ++
    (advanceTrace (erasedLeft archive digits) false (true::suffix)).map (PSTRTMSeq005.rightCfg (a:=8))

def recordFinal (archive digits suffix : List Bool) : MachineState 10 :=
  PSTRTMSeq005.rightCfg (a:=8)
    (PA17TMRatArithmeticParse002.cursorState 1 (false::erasedLeft archive digits) (true::suffix))

theorem record_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom recordEraseMachine
      ⟨0,Tape.mk₂ archive (true::false::recordWord digits suffix)⟩
      (recordTrace archive digits suffix) (recordFinal archive digits suffix) := by
  have hr := PSTRTMSeq005.seq_runsFrom bodyMachine PA17TMRatArithmeticParse002.footerMachine
    ⟨0,Tape.mk₂ archive (true::false::recordWord digits suffix)⟩
    (bodyFinal archive digits suffix)
    (PA17TMRatArithmeticParse002.cursorState 1 (false::erasedLeft archive digits) (true::suffix))
    (bodyTrace archive digits suffix) (advanceTrace (erasedLeft archive digits) false (true::suffix))
    (body_runsFrom archive digits suffix) (advance_runsFrom (erasedLeft archive digits) false (true::suffix))
  simpa only [recordEraseMachine,recordTrace,recordFinal,PSTRTMSeq005.leftCfg,
    PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using hr

private theorem zeros_header (k : Nat) (archive : List Bool) :
    false::(List.replicate k false++false::false::archive) = List.replicate (k+3) false++archive := by
  calc
    _ = List.replicate (k+1) false++(List.replicate 2 false++archive) := rfl
    _ = (List.replicate (k+1) false++List.replicate 2 false)++archive :=
      (List.append_assoc _ _ _).symm
    _ = List.replicate ((k+1)+2) false++archive :=
      congrArg (fun bits : List Bool => bits++archive) (List.replicate_add (k+1) 2 false).symm
    _ = _ := rfl

theorem record_final_tape (archive digits suffix : List Bool) :
    (recordFinal archive digits suffix).Tape =
      Tape.mk₂ (List.replicate (2*digits.length+4) false++archive) (true::suffix) := by
  change Tape.mk₂ (false::(List.replicate (2*digits.length+1) false++false::false::archive)) (true::suffix) = _
  rw [zeros_header]

theorem record_final_halt (archive digits suffix : List Bool) :
    TM0.step recordEraseMachine (recordFinal archive digits suffix) = none :=
  (record_runsFrom archive digits suffix).2.2.2

theorem recordTrace_length (archive digits suffix : List Bool) :
    (recordTrace archive digits suffix).length = 4*digits.length+10 := by
  simp only [recordTrace,bodyTrace,List.length_append,List.length_map,
    clearTrace_length,fieldTrace_length,advanceTrace_length]
  omega

theorem record_prefix_space (archive digits suffix : List Bool) (prefixLength chargedLength : Nat) :
    visitedSpace recordEraseMachine chargedLength ((recordTrace archive digits suffix).take prefixLength) ≤
      chargedLength+8*digits.length+21 := by
  have hs := PSTRTMTrace002.visitedSpace_le recordEraseMachine chargedLength
    ((recordTrace archive digits suffix).take prefixLength)
  have ht := recordTrace_length archive digits suffix
  have hp : ((recordTrace archive digits suffix).take prefixLength).length ≤
      (recordTrace archive digits suffix).length := by
    simp only [List.length_take]
    omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCleanup026
