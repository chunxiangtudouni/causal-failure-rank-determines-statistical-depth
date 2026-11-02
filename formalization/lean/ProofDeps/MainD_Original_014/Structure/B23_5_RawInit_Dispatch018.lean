module
public import Common.PSTR_WordBool_RawInit_Gate003
public import Common.PSTR_SYM_FiniteRelabel_007

/-! Five statically installed finite callees. The real count gate reads
the original input and returns on the unchanged whole tape; its actual
HALT becomes one charged write-self transfer to the selected callee.
The transition table depends on the five fixed machines, never on data. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Dispatch
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicRelabel

variable (sizes : Fin 5 → Nat)
abbrev Label := Sum (Fin 25) ((tag : Fin 5) × Fin (sizes tag+1))
instance labelInhabited : Inhabited (Label sizes) := ⟨.inl 0⟩

def portTag (q : Fin 25) : Fin 5 := ⟨q.val-20,by have bound:=q.isLt; omega⟩

theorem portTag_done (tag : Fin 5) : portTag (doneLabel tag)=tag := by
  apply Fin.ext
  simp only [portTag,doneLabel,Nat.add_sub_cancel_left]

def gateCfg (cfg : MachineState 24) : TM0.Cfg Bool (Label sizes) :=
  ⟨.inl cfg.q,cfg.Tape⟩

def branchCfg (tag : Fin 5) (cfg : MachineState (sizes tag)) : TM0.Cfg Bool (Label sizes) :=
  ⟨.inr ⟨tag,cfg.q⟩,cfg.Tape⟩

def code (callees : ∀ tag, Machine (sizes tag)) : TM0.Machine Bool (Label sizes)
  | .inl q,bit => match countGateMachine q bit with
    | none => some (.inr ⟨portTag q,0⟩,.write bit)
    | some (next,op) => some (.inl next,op)
  | .inr ⟨tag,q⟩,bit => (callees tag q bit).map (fun (next,op) => (.inr ⟨tag,next⟩,op))

theorem step_gate (callees : ∀ tag, Machine (sizes tag)) (cfg : MachineState 24) :
    TM0.step (code sizes callees) (gateCfg sizes cfg)=
      match TM0.step countGateMachine cfg with
      | none => some (branchCfg sizes (portTag cfg.q) ⟨0,cfg.Tape⟩)
      | some next => some (gateCfg sizes next) := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,code,gateCfg]
    cases action : countGateMachine q tape.head with
    | none => simp [branchCfg,Tape.write_self]
    | some pair => obtain ⟨next,op⟩:=pair; cases op <;> rfl

theorem step_branch (callees : ∀ tag, Machine (sizes tag)) (tag : Fin 5)
    (cfg : MachineState (sizes tag)) :
    TM0.step (code sizes callees) (branchCfg sizes tag cfg)=
      (TM0.step (callees tag) cfg).map (branchCfg sizes tag) := by
  cases cfg with
  | mk q tape =>
    simp only [TM0.step,code,branchCfg]
    cases action : callees tag q tape.head with
    | none => rfl
    | some pair => obtain ⟨next,op⟩:=pair; cases op <;> rfl

noncomputable def support : Finset (Label sizes) := Finset.univ
noncomputable def machine (callees : ∀ tag, Machine (sizes tag)) : Machine (support sizes).card :=
  finiteMachine (code sizes callees) (support sizes)
noncomputable def liftCfg (cfg : TM0.Cfg Bool (Label sizes)) : MachineState (support sizes).card :=
  relabelCfg (finiteLabels (support sizes)) cfg

theorem closed (callees : ∀ tag, Machine (sizes tag)) :
    TM0.Supports (code sizes callees) (support sizes : Set (Label sizes)) := by
  constructor
  · exact Finset.mem_univ _
  · intro q bit next op _ _
    exact Finset.mem_univ _

theorem actual (callees : ∀ tag, Machine (sizes tag)) (data : List Datum)
    (back : List (MachineState (sizes (countTag data.length))))
    (backFinal : MachineState (sizes (countTag data.length)))
    (backRun : Runs (callees (countTag data.length)) (encode data) back backFinal) :
    ∃ path, Runs (machine sizes callees) (encode data) path
      (liftCfg sizes (branchCfg sizes (countTag data.length) backFinal)) ∧
      path.length≤back.length+8 := by
  classical
  obtain ⟨front,mid,frontRun,frontPort,frontTape,frontTime,_frontSpace⟩:=actual_count_gate data
  let sourcePath:=front.map (gateCfg sizes)++back.map (branchCfg sizes (countTag data.length))
  let sourceFinal:=branchCfg sizes (countTag data.length) backFinal
  have first : sourcePath.head?=some (TM0.init (encode data)) := by
    simp only [sourcePath,List.head?_append,List.head?_map,frontRun.1,Option.map_some,
      Option.some_or]
    rfl
  have chain : sourcePath.IsChain (fun before after => TM0.step (code sizes callees) before=some after) := by
    apply List.IsChain.append
    · apply (List.isChain_map _).mpr
      exact frontRun.2.1.imp (fun before after edge => by simp only [step_gate,edge])
    · apply (List.isChain_map _).mpr
      exact backRun.2.1.imp (fun before after edge => by simp only [step_branch,edge,Option.map_some])
    · intro before beforeLast after afterHead
      simp only [List.getLast?_map,frontRun.2.2.1,Option.map_some,Option.mem_some_iff] at beforeLast
      simp only [List.head?_map,backRun.1,Option.map_some,Option.mem_some_iff] at afterHead
      subst before
      subst after
      simp only [step_gate,frontRun.2.2.2.1,frontTape]
      have port : portTag mid.q=countTag data.length := by rw [frontPort,portTag_done]
      rw [port]
      rfl
  have last : sourcePath.getLast?=some sourceFinal := by
    simp only [sourcePath,sourceFinal,List.getLast?_append,List.getLast?_map,
      backRun.2.2.1,Option.map_some,Option.some_or]
  have halt : TM0.step (code sizes callees) sourceFinal=none := by
    simp only [sourceFinal,step_branch,backRun.2.2.2.1,Option.map_none]
  let path:=sourcePath.map (liftCfg sizes)
  refine ⟨path,finite_runs (code sizes callees) (support sizes) (closed sizes callees)
    (encode data) sourcePath sourceFinal first chain last halt,?_⟩
  simp only [path,sourcePath,List.length_map,List.length_append]
  omega

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.Dispatch
