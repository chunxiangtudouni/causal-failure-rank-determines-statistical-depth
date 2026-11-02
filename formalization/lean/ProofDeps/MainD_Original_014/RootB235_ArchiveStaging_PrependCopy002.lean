module
public import RootB235_ArchiveStaging_Core001

/-! A real source read, paired prepend, source return and flag restoration.
The copied bit enters finite control only through MarkSeek's actual read. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

def embed {A B : Type} (tag : A → B) (cfg : TM0.Cfg Bool A) : TM0.Cfg Bool B :=
  ⟨tag cfg.q,cfg.Tape⟩

def call {A B : Type} [Inhabited A] (source : TM0.Machine Bool A)
    (tag finish : A → B) (q : A) (symbol : Bool) : Option (B × TM0.Stmt Bool) :=
  match source q symbol with
  | none => some (finish q,.write symbol)
  | some (next,op) => some (tag next,op)

theorem call_step {A B : Type} [Inhabited A] [Inhabited B]
    (whole : TM0.Machine Bool B) (source : TM0.Machine Bool A) (tag finish : A → B)
    (lookup : ∀ q bit,whole (tag q) bit=call source tag finish q bit) (cfg : TM0.Cfg Bool A) :
    TM0.step whole (embed tag cfg)=
      match TM0.step source cfg with
      | none => some ⟨finish cfg.q,cfg.Tape⟩
      | some next => some (embed tag next) := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,embed,lookup,call]
    cases action : source q tape.head with
    | none => simp only [Option.map_none,Option.map_some,Tape.write_self]
    | some pair => obtain ⟨next,op⟩ := pair; cases op <;> rfl

def call_segment {A B : Type} [Inhabited A] [Inhabited B]
    (whole : TM0.Machine Bool B) (source : TM0.Machine Bool A) (tag finish : A → B)
    (lookup : ∀ q bit,whole (tag q) bit=call source tag finish q bit)
    (first last : TM0.Cfg Bool A) (path : List (TM0.Cfg Bool A))
    (head : path.head?=some first)
    (chain : path.IsChain (fun a b => TM0.step source a=some b))
    (tail : path.getLast?=some last) (halt : TM0.step source last=none) :
    Segment whole (embed tag first) ⟨finish last.q,last.Tape⟩ (path.length+2) := by
  let front : Segment whole (embed tag first) (embed tag last) path.length :=
    ⟨path.map (embed tag),by simp only [List.head?_map,head,Option.map_some],
      (List.isChain_map _).mpr (chain.imp (fun a b step => by
        simp only [call_step whole source tag finish lookup,step])),
      by simp only [List.getLast?_map,tail,Option.map_some],by simp only [List.length_map];rfl⟩
  have edge : TM0.step whole (embed tag last)=some ⟨finish last.q,last.Tape⟩ := by
    simp only [call_step whole source tag finish lookup,halt]
  exact front.trans (Segment.edge edge)

namespace PrependCopy

inductive Label where
  | seek : Fin 15 → Label
  | output : PairPrepend.Label → Label
  | leave
  | returning
  | restore : Fin 5 → Label
  | done
  deriving DecidableEq,Fintype

instance : Inhabited Label := ⟨.seek 0⟩

def seekFinish (q : Fin 15) : Label := .output (.entry (decide (8≤q.val)))

def code : TM0.Machine Bool Label
  | .seek q,symbol => call MarkSeek.machine .seek seekFinish q symbol
  | .output q,symbol => call PairPrepend.code .output (fun _ => .leave) q symbol
  | .leave,_ => some (.returning,.move .left)
  | .returning,symbol => if symbol then some (.restore 0,.write true)
      else some (.returning,.move .left)
  | .restore q,symbol => call Restore.machine .restore (fun _ => .done) q symbol
  | .done,_ => none

def state (q : Label) (left right : List Bool) : TM0.Cfg Bool Label := ⟨q,Tape.mk₂ left right⟩

def backZeros (left right : List Bool) (gap : Nat) :
    Segment code (state .returning (List.replicate gap false++true::left) (false::right))
      (state (.restore 0) left (true::(List.replicate (gap+1) false++right))) (2*gap+4) := by
  induction gap generalizing right with
  | zero =>
    have a : TM0.step code (state .returning (true::left) (false::right))=
        some (state .returning left (true::false::right)) := by
      simp [state,code,TM0.step,Tape.mk₂]
    have b : TM0.step code (state .returning left (true::false::right))=
        some (state (.restore 0) left (true::false::right)) := by
      simp [state,code,TM0.step,Tape.mk₂]
    exact (Segment.edge a).trans (Segment.edge b)
  | succ gap ih =>
    have a : TM0.step code
        (state .returning (List.replicate (gap+1) false++true::left) (false::right))=
        some (state .returning (List.replicate gap false++true::left) (false::false::right)) := by
      simp [state,code,TM0.step,Tape.mk₂,List.replicate_succ]
    have rest := ih (false::right)
    have result := (Segment.edge a).trans rest
    have padding : List.replicate (gap+1) false++false::right=
        List.replicate (gap+1+1) false++right := by
      rw [ReverseCleanup.zeros_succ,List.replicate_succ]
      rfl
    simpa only [padding] using result.weaken (by omega)

def initial (left higher : List Bool) (bit : Bool) (gap : Nat) (output : List Bool) : TM0.Cfg Bool Label :=
  embed .seek (MarkSeek.initial left higher bit gap (true::(MarkSeek.pairs output++[true])))

def final (left higher : List Bool) (bit : Bool) (gap : Nat) (output : List Bool) : TM0.Cfg Bool Label :=
  ⟨.done,(Restore.final left higher bit
    (true::false::(List.replicate gap false++PairPrepend.word (bit::output)))).Tape⟩

theorem actual (left higher : List Bool) (bit : Bool) (gap : Nat) (output : List Bool) :
    ∃ path : List (TM0.Cfg Bool Label), path.head?=some (initial left higher bit gap output) ∧
      path.IsChain (fun a b => TM0.step code a=some b) ∧
      path.getLast?=some (final left higher bit gap output) ∧
      TM0.step code (final left higher bit gap output)=none ∧
      path.length≤4*higher.length+3*gap+10*output.length+60 := by
  obtain ⟨seekPath,seekRun,seekTime,_seekSpace⟩ :=
    MarkSeek.actual left higher bit gap (true::(MarkSeek.pairs output++[true])) 0
  have selected := call_segment code MarkSeek.machine Label.seek seekFinish
    (by intro q symbol;rfl) _ _ seekPath seekRun.1 seekRun.2.1 seekRun.2.2.1 seekRun.2.2.2
  let selectedLeft := MarkSeek.selectedLeft left higher bit
  let outputLeft := List.replicate gap false++false::true::selectedLeft
  have selectedEnd : ⟨seekFinish (MarkSeek.finish left higher bit gap
        (true::(MarkSeek.pairs output++[true]))).q,
      (MarkSeek.finish left higher bit gap (true::(MarkSeek.pairs output++[true]))).Tape⟩ =
        embed Label.output (PairPrepend.state (.entry bit) outputLeft (PairPrepend.word output)) := by
    cases bit <;> rfl
  rw [selectedEnd] at selected
  obtain ⟨outPath,outHead,outChain,outTail,outHalt,outTime⟩ := PairPrepend.actual outputLeft output bit
  have copied := call_segment code PairPrepend.code Label.output (fun _ => Label.leave)
    (by intro q symbol;rfl) _ _ outPath outHead outChain outTail outHalt
  let newOutput := PairPrepend.word (bit::output)
  have leaveStep : TM0.step code (state .leave outputLeft newOutput)=
      some (state .returning (List.replicate gap false++true::selectedLeft) (false::newOutput)) := by
    have padding : List.replicate gap false++false::true::selectedLeft=
        false::(List.replicate gap false++true::selectedLeft) :=
      ReverseCleanup.zeros_succ gap (true::selectedLeft)
    simp only [state,TM0.step,code,Option.map_some,outputLeft,padding,Tape.mk₂]
    rfl
  have returned := backZeros selectedLeft newOutput gap
  obtain ⟨restorePath,restoreRun,restoreTime,_restoreSpace⟩ :=
    Restore.actual left higher bit (true::false::(List.replicate gap false++newOutput)) 0
  have restored := call_segment code Restore.machine Label.restore (fun _ => Label.done)
    (by intro q symbol;rfl) _ _ restorePath restoreRun.1 restoreRun.2.1 restoreRun.2.2.1 restoreRun.2.2.2
  have restoredStart : embed Label.restore (Restore.initial left higher bit
      (true::false::(List.replicate gap false++newOutput)))=
        state (.restore 0) selectedLeft (true::(List.replicate (gap+1) false++newOutput)) := by
    rfl
  rw [restoredStart] at restored
  have whole := (((selected.trans copied).trans (Segment.edge leaveStep)).trans returned).trans restored
  have result : Segment code (initial left higher bit gap output) (final left higher bit gap output)
      (4*higher.length+3*gap+10*output.length+60) :=
    whole.weaken (by rw [seekTime,restoreTime];omega)
  exact ⟨result.trace,result.head,result.chain,result.tail,
    by simp [final,TM0.step,code],result.time⟩

end PrependCopy
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
