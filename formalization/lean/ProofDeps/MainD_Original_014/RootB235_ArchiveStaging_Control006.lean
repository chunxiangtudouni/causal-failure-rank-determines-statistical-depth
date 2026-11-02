module
public import RootB235_ArchiveStaging_Execution005
public import RootB235_ArchiveStaging_Terminal004
public import RootB235_ArchiveStaging_Unary_Number001

/-! The fixed finite full archive serializer control graph. All source
tag, boundary, flag and digit choices are physical Bool reads. The count
bank is preserved by the input producer and read here after work erasure.
Correctness of the complete graph is established by the following modules. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicRelabel

namespace Control

def program (q : Fin 98) : Macro.Instruction (Fin 98) :=
  match q.val with
  | 0 => .branch 1 20
  | 1 => .action (.move .left) 2
  | 2 => .action (.move .left) 3
  | 3 => .action (.move .left) 4
  | 4 => .branch 5 60
  | 5 => .action (.move .right) 6
  | 6 => .action (.move .right) 7
  | 7 => .action (.move .right) 8
  | 8 => .action (.move .left) 9
  | 9 => .action (.write false) 10
  | 10 => .action (.move .right) 11
  | 11 => .action (.write false) 12
  | 12 => .action (.move .left) 13
  | 13 => .action (.move .left) 14
  | 15 => .export .emitFalse 0
  | 20 => .action (.move .left) 21
  | 21 => .action (.move .left) 22
  | 22 => .action (.move .left) 23
  | 23 => .branch 24 26
  | 24 => .action (.move .left) 25
  | 25 => .action (.move .left) 23
  | 26 => .action (.write false) 27
  | 27 => .action (.move .left) 28
  | 28 => .action (.move .left) 29
  | 29 => .action (.write true) 30
  | 30 => .action (.move .right) 31
  | 31 => .action (.move .right) 32
  | 32 => .branch 33 35
  | 33 => .action (.move .right) 34
  | 34 => .action (.move .right) 32
  | 35 => .action (.write false) 36
  | 36 => .action (.move .right) 37
  | 37 => .action (.write false) 38
  | 38 => .action (.move .left) 39
  | 39 => .action (.move .left) 40
  | 41 => .action (.move .left) 42
  | 42 => .action (.move .left) 43
  | 43 => .action (.move .left) 44
  | 44 => .branch 45 47
  | 45 => .action (.move .left) 46
  | 46 => .action (.move .left) 44
  | 47 => .action (.move .right) 48
  | 48 => .action (.move .right) 49
  | 49 => .action (.write true) 50
  | 50 => .action (.move .right) 51
  | 51 => .action (.move .right) 52
  | 52 => .branch 53 55
  | 53 => .action (.move .right) 54
  | 54 => .action (.move .right) 52
  | 55 => .action (.write false) 56
  | 56 => .action (.move .right) 57
  | 58 => .action (.move .left) 59
  | 59 => .action (.write false) 65
  | 60 => .action (.move .right) 61
  | 61 => .action (.move .right) 62
  | 62 => .action (.move .right) 70
  | 65 => .action (.move .right) 66
  | 66 => .export .preserve 67
  | 67 => .export .emitTrue 68
  | 68 => .action (.move .left) 69
  | 69 => .action (.move .left) 0
  | 70 => .action (.move .left) 71
  | 71 => .branch 76 72
  | 72 => .action (.write false) 73
  | 73 => .action (.move .left) 74
  | 74 => .action (.write false) 75
  | 75 => .action (.move .left) 71
  | 76 => .action (.move .left) 77
  | 77 => .action (.move .left) 78
  | 78 => .action (.move .left) 79
  | 79 => .action (.move .left) 80
  | 80 => .branch 84 81
  | 81 => .action (.write false) 82
  | 82 => .action (.move .left) 83
  | 83 => .action (.move .left) 80
  | 84 => .action (.move .left) 85
  | 85 => .action (.move .left) 86
  | 86 => .action (.write true) 87
  | 87 => .action (.move .right) 88
  | 88 => .action (.move .right) 89
  | 89 => .branch 90 92
  | 90 => .action (.move .right) 91
  | 91 => .action (.move .right) 89
  | 92 => .action (.write false) 93
  | 93 => .action (.move .left) 94
  | 95 => .action (.write true) 96
  | 97 => .action (.move .left) 25
  | _ => .halt

def fieldNext (context : Fin 4) : Fin 98 :=
  match context.val with
  | 0 => 15
  | 1 => 41
  | 2 => 58
  | _ => 95

inductive Label where
  | entry
  | boot : Fin 16 → Label
  | control : Macro.Label (Fin 98) → Label
  | field : Fin 4 → NumberField.Label → Label
  | terminal : Fin 26 → Label
  | done
  deriving DecidableEq

noncomputable instance : Fintype Label := derive_fintype% _

instance : Inhabited Label := ⟨.entry⟩

def controlFinish : Macro.Label (Fin 98) → Label
  | .at q =>
    match q.val with
    | 14 => .field 0 (.at 0)
    | 40 => .field 1 (.at 0)
    | 57 => .field 2 (.at 0)
    | 94 => .field 3 (.at 0)
    | 96 => .terminal 0
    | _ => .done
  | _ => .done

def code : TM0.Machine Bool Label
  | .entry,symbol => some (.boot 2,.write symbol)
  | .boot q,symbol => call Terminal.stageMachine .boot (fun _ => .control (.at 0)) q symbol
  | .control q,symbol => call (Macro.code program) .control controlFinish q symbol
  | .field context q,symbol => call NumberField.code (.field context)
      (fun _ => .control (.at (fieldNext context))) q symbol
  | .terminal q,symbol => call Terminal.machine .terminal (fun _ => .done) q symbol
  | .done,_ => none

def state (loc : Fin 98) (tape : Tape Bool) : TM0.Cfg Bool Label := ⟨.control (.at loc),tape⟩

def cfg (loc : Fin 98) (left higher output : List Bool) (flag bit : Bool) (gap : Nat) :
    TM0.Cfg Bool Label := state loc (Macro.source left higher output flag bit gap)

def liftControl {first last : TM0.Cfg Bool (Macro.Label (Fin 98))} {budget : Nat}
    (path : Segment (Macro.code program) first last budget) :
    Segment code (embed Label.control first) (embed Label.control last) budget :=
  call_map_segment code (Macro.code program) Label.control controlFinish (by intro q bit;rfl) path

noncomputable def fieldRun (port : Fin 98) (context : Fin 4)
    (isPort : program port=.halt) (selected : controlFinish (.at port)=.field context (.at 0))
    (left higher output : List Bool) (boundary : Bool) (gap : Nat) (digits : List Bool) :
    Segment code (state port (NumberField.input left higher output boundary gap digits).Tape)
      (state (fieldNext context) (NumberField.finish left higher output boundary gap digits).Tape)
      (1000*(digits.length+higher.length+output.length+gap+1)^2+4) := by
  have inputQ : (NumberField.input left higher output boundary gap digits).q=(.at 0) := by
    unfold NumberField.input
    cases digits.reverse <;> rfl
  have enter : TM0.step code (state port (NumberField.input left higher output boundary gap digits).Tape)=
      some (embed (Label.field context) (NumberField.input left higher output boundary gap digits)) := by
    simp only [state,TM0.step,code,call,Macro.code,isPort,selected,Option.map_some,Tape.write_self,embed,inputQ]
  have middle := call_map_segment code NumberField.code (Label.field context)
    (fun _ => Label.control (.at (fieldNext context))) (by intro q bit;rfl)
    (NumberField.actual left higher output boundary gap digits)
  have leave : TM0.step code (embed (Label.field context)
      (NumberField.finish left higher output boundary gap digits))=
        some (state (fieldNext context) (NumberField.finish left higher output boundary gap digits).Tape) := by
    simp only [call_step code NumberField.code (Label.field context)
      (fun _ => Label.control (.at (fieldNext context))) (by intro q bit;rfl),NumberField.halt,state]
  exact ((Segment.edge enter).trans middle).trans (Segment.edge leave) |>.weaken (by omega)

def naturalTape (left digits higher output : List Bool) (boundary : Bool) (gap : Nat) : Tape Bool :=
  Macro.source (Restore.reversePairs digits.reverse++boundary::true::left) higher output true false gap

def naturalEntry (left digits higher output : List Bool) (boundary : Bool) (gap : Nat)
    (nonempty : digits≠[]) :
    Segment code (state 0 (naturalTape left digits higher output boundary gap))
      (state 14 (NumberField.input left higher output boundary gap digits).Tape) 29 := by
  apply follow_actual code 14
  cases shape : digits.reverse with
  | nil =>
    have empty := congrArg List.reverse shape
    simp only [List.reverse_reverse,List.reverse_nil] at empty
    exact False.elim (nonempty empty)
  | cons bit older =>
    simp [follow,code,call,program,state,naturalTape,Macro.code,Macro.source,Macro.suffix,
      NumberField.input,NumberField.loopCfg,NumberField.cfg,Macro.cfg,Restore.reversePairs,
      shape,TM0.step,Tape.mk₂,MarkSeek.pairs]

noncomputable def natural (left digits higher output : List Bool) (boundary : Bool) (gap : Nat)
    (nonempty : digits≠[]) :
    Segment code (state 0 (naturalTape left digits higher output boundary gap))
      (cfg 0 left (List.replicate (digits.length+1) false++higher)
        (false::(List.replicate digits.length true++false::(digits++output))) true boundary gap)
      (2000*(digits.length+higher.length+output.length+gap+1)^2) := by
  have front := naturalEntry left digits higher output boundary gap nonempty
  have field := fieldRun 14 0 rfl rfl left higher output boundary gap digits
  let newHigher := List.replicate (digits.length+1) false++higher
  let newOutput := List.replicate digits.length true++false::(digits++output)
  have tag := liftControl (Macro.export_actual program 15 0 .emitFalse rfl left newHigher newOutput true boundary gap)
  have result := (front.trans field).trans tag
  exact result.weaken (by
    simp only [newHigher,newOutput,List.length_append,List.length_replicate,List.length_cons]
    nlinarith [Nat.zero_le (digits.length^2),Nat.zero_le (higher.length^2),
      Nat.zero_le (output.length^2),Nat.zero_le (gap^2)])

noncomputable def support : Finset Label := Finset.univ
noncomputable def machine : Machine support.card := finiteMachine code support
noncomputable def haltPort : Fin (support.card+1) := finiteLabels support .done

end Control
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
