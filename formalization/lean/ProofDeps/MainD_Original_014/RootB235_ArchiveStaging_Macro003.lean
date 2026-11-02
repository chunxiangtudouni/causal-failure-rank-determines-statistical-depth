module
public import RootB235_ArchiveStaging_PrependCopy002

/-! Finite physical macros. Export temporarily clears the real source flag,
calls the one-read prepend machine, and restores/marks the actual cells.
Only two original source bits are retained in finite control. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

namespace Macro

inductive Mode where
  | preserve
  | digit
  | unary
  | emitFalse
  | emitTrue
  deriving DecidableEq

instance : Fintype Mode := ⟨{.preserve,.digit,.unary,.emitFalse,.emitTrue},by
  intro mode;cases mode <;> simp⟩

def exported : Mode → Bool → Bool
  | .preserve,bit => bit
  | .digit,bit => bit
  | .unary,_ => true
  | .emitFalse,_ => false
  | .emitTrue,_ => true

def finalFlag : Mode → Bool → Bool
  | .digit,_ => false
  | .unary,_ => false
  | _,flag => flag

def finalBit : Mode → Bool → Bool
  | .digit,_ => true
  | .unary,_ => false
  | _,bit => bit

inductive Instruction (L : Type) where
  | action : TM0.Stmt Bool → L → Instruction L
  | branch : L → L → Instruction L
  | export : Mode → L → Instruction L
  | halt

inductive Label (L : Type) where
  | at : L → Label L
  | saveFlag : L → Mode → Bool → Label L
  | toPayload : L → Mode → Bool → Bool → Label L
  | put : L → Mode → Bool → Bool → Label L
  | copy : L → Mode → Bool → Bool → PrependCopy.Label → Label L
  | after : L → Mode → Bool → Bool → Label L
  | restoreFlag : L → Mode → Bool → Bool → Label L
  | toBit : L → Mode → Bool → Bool → Label L
  | restoreBit : L → Mode → Bool → Bool → Label L
  deriving DecidableEq

def labelCode {L : Type} : Label L → L × Fin 9 × Mode × Bool × Bool × PrependCopy.Label
  | .at loc => (loc,0,.preserve,false,false,.seek 0)
  | .saveFlag loc mode bit => (loc,1,mode,bit,false,.seek 0)
  | .toPayload loc mode bit flag => (loc,2,mode,bit,flag,.seek 0)
  | .put loc mode bit flag => (loc,3,mode,bit,flag,.seek 0)
  | .copy loc mode bit flag point => (loc,4,mode,bit,flag,point)
  | .after loc mode bit flag => (loc,5,mode,bit,flag,.seek 0)
  | .restoreFlag loc mode bit flag => (loc,6,mode,bit,flag,.seek 0)
  | .toBit loc mode bit flag => (loc,7,mode,bit,flag,.seek 0)
  | .restoreBit loc mode bit flag => (loc,8,mode,bit,flag,.seek 0)

def labelDecode {L : Type} : L × Fin 9 × Mode × Bool × Bool × PrependCopy.Label → Label L
  | (loc,phase,mode,bit,flag,point) =>
    match phase.val with
    | 0 => .at loc
    | 1 => .saveFlag loc mode bit
    | 2 => .toPayload loc mode bit flag
    | 3 => .put loc mode bit flag
    | 4 => .copy loc mode bit flag point
    | 5 => .after loc mode bit flag
    | 6 => .restoreFlag loc mode bit flag
    | 7 => .toBit loc mode bit flag
    | _ => .restoreBit loc mode bit flag

theorem labelDecode_code {L : Type} (q : Label L) : labelDecode (labelCode q)=q := by
  cases q <;> rfl

noncomputable instance {L : Type} [Fintype L] : Fintype (Label L) :=
  Fintype.ofInjective labelCode (by
    intro a b same
    have decoded := congrArg labelDecode same
    simpa only [labelDecode_code] using decoded)

instance {L : Type} [Inhabited L] : Inhabited (Label L) := ⟨.at default⟩

def code {L : Type} [Inhabited L] (program : L → Instruction L) : TM0.Machine Bool (Label L)
  | .at loc,symbol =>
    match program loc with
    | .action op next => some (.at next,op)
    | .branch no yes => some (.at (if symbol then yes else no),.write symbol)
    | .export mode next => some (.saveFlag next mode symbol,.move .left)
    | .halt => none
  | .saveFlag next mode bit,flag => some (.toPayload next mode bit flag,.write false)
  | .toPayload next mode bit flag,_ => some (.put next mode bit flag,.move .right)
  | .put next mode bit flag,_ =>
      some (.copy next mode bit flag (.seek 0),.write (exported mode bit))
  | .copy next mode bit flag q,symbol => call PrependCopy.code (.copy next mode bit flag)
      (fun _ => .after next mode bit flag) q symbol
  | .after next mode bit flag,_ => some (.restoreFlag next mode bit flag,.move .right)
  | .restoreFlag next mode bit flag,_ => some (.toBit next mode bit flag,.write (finalFlag mode flag))
  | .toBit next mode bit flag,_ => some (.restoreBit next mode bit flag,.move .right)
  | .restoreBit next mode bit _,_ => some (.at next,.write (finalBit mode bit))

def suffix (higher output : List Bool) (gap : Nat) : List Bool :=
  MarkSeek.pairs higher++true::false::(List.replicate gap false++PairPrepend.word output)

def source (left higher output : List Bool) (flag bit : Bool) (gap : Nat) : Tape Bool :=
  Tape.mk₂ (flag::left) (bit::suffix higher output gap)

def cfg {L : Type} (loc : L) (left higher output : List Bool) (flag bit : Bool) (gap : Nat) :
    TM0.Cfg Bool (Label L) := ⟨.at loc,source left higher output flag bit gap⟩

noncomputable def export_actual {L : Type} [Inhabited L] (program : L → Instruction L)
    (loc next : L) (mode : Mode) (selected : program loc=.export mode next)
    (left higher output : List Bool) (flag bit : Bool) (gap : Nat) :
    Segment (code program) (cfg loc left higher output flag bit gap)
      (cfg next left higher (exported mode bit::output) (finalFlag mode flag) (finalBit mode bit) gap)
      (4*higher.length+3*gap+10*output.length+80) := by
  let a := cfg loc left higher output flag bit gap
  let b : TM0.Cfg Bool (Label L) :=
    ⟨.saveFlag next mode bit,Tape.mk₂ left (flag::bit::suffix higher output gap)⟩
  let c : TM0.Cfg Bool (Label L) :=
    ⟨.toPayload next mode bit flag,Tape.mk₂ left (false::bit::suffix higher output gap)⟩
  let d : TM0.Cfg Bool (Label L) :=
    ⟨.put next mode bit flag,source left higher output false bit gap⟩
  let e := embed (Label.copy next mode bit flag)
    (PrependCopy.initial left higher (exported mode bit) gap output)
  have ab : TM0.step (code program) a=some b := by
    simp [a,b,cfg,source,TM0.step,code,selected,Tape.mk₂]
  have bc : TM0.step (code program) b=some c := by simp [b,c,TM0.step,code,Tape.mk₂]
  have cd : TM0.step (code program) c=some d := by simp [c,d,source,TM0.step,code,Tape.mk₂]
  have de : TM0.step (code program) d=some e := by
    simp [d,e,source,suffix,PrependCopy.initial,MarkSeek.initial,embed,TM0.step,code,Tape.mk₂,PairPrepend.word]
  let result := PrependCopy.actual left higher (exported mode bit) gap output
  let copiedPath := Classical.choose result
  have copiedProof := Classical.choose_spec result
  obtain ⟨copiedHead,copiedChain,copiedTail,copiedHalt,copiedTime⟩ := copiedProof
  change copiedPath.length≤4*higher.length+3*gap+10*output.length+60 at copiedTime
  have copied := call_segment (code program) PrependCopy.code (Label.copy next mode bit flag)
    (fun _ => Label.after next mode bit flag) (by intro q symbol;rfl) _ _ copiedPath
    copiedHead copiedChain copiedTail copiedHalt
  let tail := suffix higher (exported mode bit::output) gap
  let f : TM0.Cfg Bool (Label L) :=
    ⟨.after next mode bit flag,(Tape.mk₂ left (false::exported mode bit::tail)).move .left⟩
  let g : TM0.Cfg Bool (Label L) :=
    ⟨.restoreFlag next mode bit flag,Tape.mk₂ left (false::exported mode bit::tail)⟩
  let h : TM0.Cfg Bool (Label L) :=
    ⟨.toBit next mode bit flag,Tape.mk₂ left (finalFlag mode flag::exported mode bit::tail)⟩
  let i : TM0.Cfg Bool (Label L) :=
    ⟨.restoreBit next mode bit flag,source left higher (exported mode bit::output)
      (finalFlag mode flag) (exported mode bit) gap⟩
  let j := cfg next left higher (exported mode bit::output) (finalFlag mode flag) (finalBit mode bit) gap
  have fg : TM0.step (code program) f=some g := by
    simp only [f,g,TM0.step,code,Option.map_some,Tape.move_left_right]
  have gh : TM0.step (code program) g=some h := by simp [g,h,TM0.step,code,Tape.mk₂]
  have hi : TM0.step (code program) h=some i := by simp [h,i,source,tail,TM0.step,code,Tape.mk₂]
  have ij : TM0.step (code program) i=some j := by simp [i,j,cfg,source,TM0.step,code,Tape.mk₂]
  have middle : Segment (code program) e f (copiedPath.length+2) := copied
  have result := (((((((Segment.edge ab).trans (Segment.edge bc)).trans (Segment.edge cd)).trans
    (Segment.edge de)).trans middle).trans (Segment.edge fg)).trans (Segment.edge gh)).trans
    ((Segment.edge hi).trans (Segment.edge ij))
  exact result.weaken (by omega)

end Macro
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
