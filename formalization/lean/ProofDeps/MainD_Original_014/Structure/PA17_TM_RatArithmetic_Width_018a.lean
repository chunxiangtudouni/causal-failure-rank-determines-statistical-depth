module
public import Structure.PA17_TM_RatArithmetic_Bookmark_014g
public import Common.ROOT_TM_GCD_CounterTrace_012

/-! Local physical operations for the width counter. A temporary FALSE
flag is created by a genuine read/clear/advance. Scanning stops on that
flag and never inspects the cell to its right. Restoring TRUE is paid. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018

def markMachine : Machine 2 := fun q symbol =>
  match q.val with
  | 0 => if symbol then some (1,.write false) else none
  | 1 => some (2,.move .right)
  | _ => none

def markState (q : Fin 3) (left right : List Bool) : MachineState 2 := ⟨q,Turing.Tape.mk₂ left right⟩

def markTrace (left tail : List Bool) : List (MachineState 2) :=
  [markState 0 left (true::tail),markState 1 left (false::tail),markState 2 (false::left) tail]

theorem mark_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom markMachine (markState 0 left (true::tail))
      (markTrace left tail) (markState 2 (false::left) tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [markTrace,List.isChain_cons_cons,Turing.TM0.step,markMachine,markState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,markMachine,markState]

theorem mark_false_halt (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom markMachine (markState 0 left (false::tail))
      [markState 0 left (false::tail)] (markState 0 left (false::tail)) := by
  refine ⟨rfl,by simp,rfl,?_⟩
  simp [Turing.TM0.step,markMachine,markState,Turing.Tape.mk₂]

def scanMachine : Machine 1 := fun q symbol =>
  if q.val=0 then some (1,.move .right)
  else if symbol then some (0,.move .right) else none

def scanState (q : Fin 2) (left right : List Bool) : MachineState 1 := ⟨q,Turing.Tape.mk₂ left right⟩

def scanTrace (left : List Bool) : List Bool → Bool → List Bool → List (MachineState 1)
  | [],bit,tail => [scanState 0 left (bit::false::tail),scanState 1 (bit::left) (false::tail)]
  | data::later,bit,tail =>
      [scanState 0 left (data::true::(PSTRTMIncrement009.blocks later++bit::false::tail)),
       scanState 1 (data::left) (true::(PSTRTMIncrement009.blocks later++bit::false::tail))] ++
      scanTrace (true::data::left) later bit tail

theorem scan_head (left digits : List Bool) (bit : Bool) (tail : List Bool) :
    (scanTrace left digits bit tail).head?=
      some (scanState 0 left (PSTRTMIncrement009.blocks digits++bit::false::tail)) := by
  cases digits <;> rfl

theorem scan_last (left digits : List Bool) (bit : Bool) (tail : List Bool) :
    (scanTrace left digits bit tail).getLast?=
      some (scanState 1 (bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (false::tail)) := by
  induction digits generalizing left with
  | nil => rfl
  | cons data later ih =>
    have hne : scanTrace (true::data::left) later bit tail≠[] := by
      intro h
      have hh := scan_head (true::data::left) later bit tail
      simp [h] at hh
    simp only [scanTrace,List.cons_append,List.nil_append,List.getLast?_cons_cons]
    rw [List.getLast?_cons_of_ne_nil hne,ih]
    simp [PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem scanTrace_length (left digits : List Bool) (bit : Bool) (tail : List Bool) :
    (scanTrace left digits bit tail).length=2*digits.length+2 := by
  induction digits generalizing left with
  | nil => rfl
  | cons data later ih =>
    simp only [scanTrace,List.length_append,List.length_cons,List.length_nil,ih]
    omega

theorem scan_chain (left digits : List Bool) (bit : Bool) (tail : List Bool) :
    (scanTrace left digits bit tail).IsChain (fun a b => Turing.TM0.step scanMachine a=some b) := by
  induction digits generalizing left with
  | nil => simp [scanTrace,List.isChain_cons_cons,Turing.TM0.step,scanMachine,scanState,Turing.Tape.mk₂]
  | cons data later ih =>
    rw [scanTrace]
    apply List.IsChain.append
    · simp [List.isChain_cons_cons,Turing.TM0.step,scanMachine,scanState,Turing.Tape.mk₂]
    · exact ih _
    · intro before hb after ha
      simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
      simp only [scan_head,Option.mem_some_iff] at ha
      subst before
      subst after
      simp [Turing.TM0.step,scanMachine,scanState,Turing.Tape.mk₂]

theorem scan_runsFrom (left digits : List Bool) (bit : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom scanMachine
      (scanState 0 left (PSTRTMIncrement009.blocks digits++bit::false::tail))
      (scanTrace left digits bit tail)
      (scanState 1 (bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (false::tail)) := by
  refine ⟨scan_head left digits bit tail,scan_chain left digits bit tail,scan_last left digits bit tail,?_⟩
  simp [Turing.TM0.step,scanMachine,scanState,Turing.Tape.mk₂]

def restoreMachine : Machine 2 := fun q _ =>
  match q.val with
  | 0 => some (1,.write true)
  | 1 => some (2,.move .right)
  | _ => none

def restoreTrace (left tail : List Bool) : List (MachineState 2) :=
  [markState 0 left (false::tail),markState 1 left (true::tail),markState 2 (true::left) tail]

theorem restore_runsFrom (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom restoreMachine (markState 0 left (false::tail))
      (restoreTrace left tail) (markState 2 (true::left) tail) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [restoreTrace,List.isChain_cons_cons,Turing.TM0.step,restoreMachine,markState,Turing.Tape.mk₂]
  · simp [Turing.TM0.step,restoreMachine,markState]

def seekRestoreMachine : Machine 4 := PSTRTMSeq005.seqMachine scanMachine restoreMachine

def seekRestoreTrace (left digits : List Bool) (bit : Bool) (tail : List Bool) : List (MachineState 4) :=
  (scanTrace left digits bit tail).map (PSTRTMSeq005.leftCfg (b:=2)) ++
    (restoreTrace (bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail).map
      (PSTRTMSeq005.rightCfg (a:=1))

def seekRestoreFinal (left digits : List Bool) (bit : Bool) (tail : List Bool) : MachineState 4 :=
  PSTRTMSeq005.rightCfg (a:=1)
    (markState 2 (true::bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail)

theorem seekRestore_runsFrom (left digits : List Bool) (bit : Bool) (tail : List Bool) :
    PSTRTMSeq005.RunsFrom seekRestoreMachine
      ⟨0,Turing.Tape.mk₂ left (PSTRTMIncrement009.blocks digits++bit::false::tail)⟩
      (seekRestoreTrace left digits bit tail) (seekRestoreFinal left digits bit tail) := by
  have h := PSTRTMSeq005.seq_runsFrom scanMachine restoreMachine
    (scanState 0 left (PSTRTMIncrement009.blocks digits++bit::false::tail))
    (scanState 1 (bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) (false::tail))
    (markState 2 (true::bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail)
    (scanTrace left digits bit tail)
    (restoreTrace (bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail)
    (scan_runsFrom left digits bit tail)
    (restore_runsFrom (bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail)
  simpa only [seekRestoreMachine,seekRestoreTrace,seekRestoreFinal,scanState,
    PSTRTMSeq005.leftCfg,PSTRTMSeq005.leftLabel,Fin.val_zero,Fin.mk_zero] using h

theorem seekRestoreTrace_length (left digits : List Bool) (bit : Bool) (tail : List Bool) :
    (seekRestoreTrace left digits bit tail).length=2*digits.length+5 := by
  change (((scanTrace left digits bit tail).map (PSTRTMSeq005.leftCfg (a:=1) (b:=2))) ++
    (restoreTrace (bit::(PSTRTMRawNat010.leftBlocks digits.reverse++left)) tail).map
      (PSTRTMSeq005.rightCfg (a:=1) (b:=2))).length = _
  rw [List.length_append,List.length_map,List.length_map,scanTrace_length]
  change 2*digits.length+2+3 = _
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
