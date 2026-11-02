module
public import Structure.B23_5_RawInit_CopyRound005

/-! A fixed physical reverse-export loop for an internal staged raw-bit
source. Two TRUE boundary cells distinguish exhaustion from arbitrary TRUE
payloads. The boundary and staging layout are explicit internal ABI, not
assumptions added to the original whole RawInit target. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ReverseLoop
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005

def bodyLabel (q : Fin 420) : Fin 423 := ⟨3+q.val,by omega⟩
def bodyCfg (cfg : MachineState 419) : MachineState 422 := ⟨bodyLabel cfg.q,cfg.Tape⟩
def haltPort : Fin 423 := 2

def machine : Machine 422 := fun q symbol =>
  if q.val=0 then some (1,.move .left)
  else if q.val=1 then some ((if symbol then haltPort else bodyLabel 0),.move .right)
  else if q.val=2 then none
  else
    match CopyRound.machine ⟨q.val-3,by omega⟩ symbol with
    | none => some (0,.write symbol)
    | some (next,op) => some (bodyLabel next,op)

theorem body_step (cfg : MachineState 419) :
    TM0.step machine (bodyCfg cfg) =
      match TM0.step CopyRound.machine cfg with
      | none => some ⟨0,cfg.Tape⟩
      | some next => some (bodyCfg next) := by
  cases cfg with
  | mk q tape =>
    have nonzero : 3+q.val≠0 := by omega
    have nonone : 3+q.val≠1 := by omega
    have nontwo : 3+q.val≠2 := by omega
    simp only [TM0.step,bodyCfg,bodyLabel,machine,nonzero,nonone,nontwo,
      ↓reduceIte,Nat.add_sub_cancel_left,Fin.eta]
    cases action : CopyRound.machine q tape.head with
    | none => simp only [Option.map_none,Option.map_some,Tape.write_self]
    | some pair => obtain ⟨next,op⟩ := pair; cases op <;> rfl

def suffix (higher output : List Bool) (gap : Nat) : List Bool :=
  MarkSeek.pairs higher ++ true :: false :: (List.replicate gap false ++ RowEnd.rows output)

def tape : List Bool → List Bool → Nat → List Bool → Tape Bool
  | [], higher, gap, output => Tape.mk₂ [true] (true :: suffix higher output gap)
  | bit :: later, higher, gap, output =>
      Tape.mk₂ (false :: (Restore.reversePairs later ++ [true,true]))
        (bit :: suffix higher output gap)

def state (remaining higher : List Bool) (gap : Nat) (output : List Bool) : MachineState 422 :=
  ⟨0,tape remaining higher gap output⟩

def finish (higher : List Bool) (gap : Nat) (output : List Bool) : MachineState 422 :=
  ⟨haltPort,tape [] higher gap output⟩

theorem copy_initial (bit : Bool) (later higher output : List Bool) (gap : Nat) :
    CopyRound.initial (Restore.reversePairs later ++ [true,true]) higher bit gap output =
      ⟨0,tape (bit::later) higher gap output⟩ := by
  rfl

theorem copy_final_tape (bit : Bool) (later higher output : List Bool) (gap : Nat) :
    (CopyRound.final (Restore.reversePairs later ++ [true,true]) higher bit gap output).Tape =
      tape later (bit::higher) gap (output++[bit]) := by
  cases later with
  | nil =>
    simp [CopyRound.final,rightCfg,Restore.final,Restore.reversePairs,MarkSeek.pairs,
      tape,suffix,CopyRound.outputSuffix,List.replicate_succ,Tape.mk₂]
  | cons first rest =>
    simp [CopyRound.final,rightCfg,Restore.final,Restore.reversePairs,MarkSeek.pairs,
      tape,suffix,CopyRound.outputSuffix,List.replicate_succ,Tape.mk₂]

theorem selector_step (bit : Bool) (later higher output : List Bool) (gap : Nat) :
    TM0.step machine (state (bit::later) higher gap output) =
      some ⟨1,(tape (bit::later) higher gap output).move .left⟩ ∧
    TM0.step machine ⟨1,(tape (bit::later) higher gap output).move .left⟩ =
      some (bodyCfg (CopyRound.initial (Restore.reversePairs later++[true,true])
        higher bit gap output)) := by
  constructor
  · simp [state,TM0.step,machine]
  · simp [tape,TM0.step,machine,bodyCfg,bodyLabel,CopyRound.initial,
      leftCfg,leftLabel,MarkAppend.initial,MarkSeek.pairs,suffix,Tape.mk₂]

theorem boundary_run (higher output : List Bool) (gap : Nat) :
    RunsFrom machine (state [] higher gap output)
      [state [] higher gap output,
       ⟨1,(tape [] higher gap output).move .left⟩,finish higher gap output]
      (finish higher gap output) := by
  refine ⟨rfl,?_,rfl,?_⟩
  · simp [List.isChain_cons_cons,state,finish,tape,TM0.step,machine,haltPort,Tape.mk₂]
  · simp [finish,TM0.step,machine,haltPort]

def cost (higher output : Nat) : Nat → Nat
  | 0 => 3
  | n+1 => 4*higher + 67*(output+1) + 120 + cost (higher+1) (output+1) n

theorem actual (remaining higher output : List Bool) (gap : Nat) :
    ∃ path, RunsFrom machine (state remaining higher gap output) path
        (finish (remaining.reverse++higher) gap (output++remaining)) ∧
      path.length = cost higher.length output.length remaining.length + 2*gap*remaining.length := by
  induction remaining generalizing higher output with
  | nil =>
    refine ⟨[state [] higher gap output,
      ⟨1,(tape [] higher gap output).move .left⟩,finish higher gap output],?_,?_⟩
    · simpa only [List.reverse_nil,List.nil_append,List.append_nil] using boundary_run higher output gap
    · simp only [List.length_cons,List.length_nil,cost,Nat.mul_zero,Nat.add_zero]
  | cons bit later ih =>
    obtain ⟨body,bodyRun,bodyTime,_bodySpace⟩ :=
      CopyRound.actual (Restore.reversePairs later++[true,true]) higher bit gap output 0
    obtain ⟨tail,tailRun,tailTime⟩ := ih (bit::higher) (output++[bit])
    let point := state (bit::later) higher gap output
    let probe : MachineState 422 := ⟨1,(tape (bit::later) higher gap output).move .left⟩
    let front := [point,probe]++body.map bodyCfg
    have frontChain : front.IsChain (fun before after => TM0.step machine before=some after) := by
      apply List.IsChain.append
      · apply List.isChain_cons_cons.mpr
        exact ⟨(selector_step bit later higher output gap).1,.singleton _⟩
      · apply (List.isChain_map _).mpr
        exact bodyRun.2.1.imp (fun before after edge => by simp only [body_step,edge])
      · intro before hb after ha
        simp only [List.getLast?_cons_cons,List.getLast?_singleton,Option.mem_some_iff] at hb
        simp only [List.head?_map,bodyRun.1,Option.map_some,Option.mem_some_iff] at ha
        subst before; subst after
        exact (selector_step bit later higher output gap).2
    have frontLast : front.getLast?=some (bodyCfg
        (CopyRound.final (Restore.reversePairs later++[true,true]) higher bit gap output)) := by
      simp only [front,List.getLast?_append,List.getLast?_map,bodyRun.2.2.1,Option.map_some,Option.some_or]
    have chain : (front++tail).IsChain (fun before after => TM0.step machine before=some after) := by
      apply List.IsChain.append frontChain tailRun.2.1
      intro before hb after ha
      simp only [frontLast,Option.mem_some_iff] at hb
      simp only [tailRun.1,Option.mem_some_iff] at ha
      subst before; subst after
      simp only [body_step,bodyRun.2.2.2,copy_final_tape,state]
    have halt := tailRun.2.2.2
    refine ⟨front++tail,⟨?_,chain,?_,?_⟩,?_⟩
    · simp only [List.head?_append,front,List.head?_cons,Option.some_or,point]
    · simp only [List.getLast?_append,tailRun.2.2.1,Option.some_or,
        List.reverse_cons,List.append_assoc,List.singleton_append]
    · simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using halt
    · simp only [List.length_cons,List.length_append] at tailTime
      simp only [List.length_append,front,List.length_cons,List.length_nil,List.length_map,
        bodyTime,tailTime,cost,Nat.mul_add,Nat.mul_one,Nat.zero_add]
      omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ReverseLoop
