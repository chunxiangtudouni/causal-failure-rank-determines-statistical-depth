module

public import Paid.PDROC_BitVM_Kernel_Register_001
public import Paid.PDROC_BitVM_Native_Frame_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Kernel.RegisterGlobal

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Native

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev State := TM2.Cfg Alphabet RegisterMove.Label RegisterMove.Store

/-- All seven roles are compile-time choices, before any runtime word. -/
def registerSlot (reg : Register) : Stack := ⟨14+reg.word,by cases reg <;> decide⟩

theorem registerSlot_bounds (reg : Register) :
    14≤(registerSlot reg).val ∧ (registerSlot reg).val≤20 := by
  cases reg <;> decide

theorem registerSlot_injective : Function.Injective registerSlot := by
  intro a b equal
  have values := congrArg Fin.val equal
  have words : a.word=b.word := by change 14+a.word=14+b.word at values;omega
  have decoded : some a=some b := by
    rw [←PaperProofs.Structure.LaminarTree.IndexedRAM.Register.fromWord_word a,
      ←PaperProofs.Structure.LaminarTree.IndexedRAM.Register.fromWord_word b,words]
  exact Option.some.inj decoded

def moveSlot (source target : Register) (index : Fin 3) : Stack :=
  if index=0 then registerSlot source else if index=1 then registerSlot target else 24

def moveEmbedding (source target : Register) (different : source≠target) : Fin 3 ↪ Stack where
  toFun := moveSlot source target
  inj' := by
    intro a b equal
    have values := congrArg Fin.val equal
    have sourceBounds := registerSlot_bounds source
    have targetBounds := registerSlot_bounds target
    have unequal : (registerSlot source).val≠(registerSlot target).val :=
      fun same=>different (registerSlot_injective (Fin.ext same))
    fin_cases a <;> fin_cases b <;> simp [moveSlot] at values ⊢ <;> omega

def machine (source target : Register) (different : source≠target) :
    RegisterMove.Label → TM2.Stmt Alphabet RegisterMove.Label RegisterMove.Store :=
  Lift.machine (moveEmbedding source target different) RegisterMove.program

def RegistersRepresent {Λ σ : Type*} (logical : PaperProofs.Paid.Computation.State)
    (physical : TM2.Cfg Alphabet Λ σ) : Prop :=
  ∀ reg,physical.stk (registerSlot reg)=encodeCellBits (logical.register reg)

theorem move_initial_projection (source target : Register) (different : source≠target)
    (logical : PaperProofs.Paid.Computation.State) (physical : State) (store : Option Bool)
    (entry : physical.l=some 0) (saved : physical.var=(store,()))
    (represented : RegistersRepresent logical physical) (scratch : physical.stk 24=[]) :
    Lift.cfg (moveEmbedding source target different) physical=
      RegisterMove.before (encodeCellBits (logical.register source))
        (encodeCellBits (logical.register target)) store := by
  have slots : Lift.slots (moveEmbedding source target different) physical.stk=
      PDROC.BitVM.Log.TwoStack.threeStacks (encodeCellBits (logical.register source))
        (encodeCellBits (logical.register target)) [] := by
    funext index
    fin_cases index
    · exact represented source
    · exact represented target
    · exact scratch
  change (⟨physical.l,physical.var,Lift.slots (moveEmbedding source target different) physical.stk⟩ :
    RegisterMove.State)=_
  rw [entry,saved,slots]
  rfl

theorem register_outside (source target reg : Register) (different : source≠target)
    (notSource : reg≠source) (notTarget : reg≠target) :
    ∀ index,registerSlot reg≠moveEmbedding source target different index := by
  intro index
  fin_cases index
  · exact fun equal=>notSource (registerSlot_injective equal)
  · exact fun equal=>notTarget (registerSlot_injective equal)
  · intro equal
    have values := congrArg Fin.val equal
    have bounds := registerSlot_bounds reg
    change (registerSlot reg).val=24 at values
    omega

theorem supports (source target : Register) (different : source≠target) :
    TM2.Supports (machine source target different) (Finset.univ : Finset RegisterMove.Label) :=
  Lift.supports (moveEmbedding source target different) RegisterMove.program _ RegisterMove.supports

/-- Actual original RAM move on the fixed global32-stack layout. All
unselected readonly, heap and output stacks are framed by the same path.
Entry scratch emptiness is an actual caller invariant, not extra raw input. -/
theorem move_instruction_runs (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (physical : State) (source target : Register) (different : source≠target) (store : Option Bool)
    (entry : physical.l=some 0) (saved : physical.var=(store,()))
    (represented : RegistersRepresent logical physical) (scratch : physical.stk 24=[]) :
    ∃ (after : PaperProofs.Paid.Computation.State) (run : List State) (lastState : State),
      Instruction.execute input (.move target source) logical=some after ∧
      run.head?=some physical ∧
      run.IsChain (fun a b=>TM2.step (machine source target different) a=some b) ∧
      run.getLast?=some lastState ∧ TM2.step (machine source target different) lastState=none ∧
      RegistersRepresent after lastState ∧ lastState.stk 24=[] ∧
      run.length=(encodeCellBits (logical.register target)).length+
        2*(encodeCellBits (logical.register source)).length+5 ∧
      ∀ other,(∀ index,other≠moveEmbedding source target different index)→
        lastState.stk other=physical.stk other := by
  let after := ({logical with pc:=logical.pc+1}).set target (logical.register source)
  let sourceWord := encodeCellBits (logical.register source)
  let targetWord := encodeCellBits (logical.register target)
  obtain ⟨localRun,head,chain,last,halt,length,_src,_dst,_tmp⟩ :=
    RegisterMove.move_word_runs sourceWord targetWord store
  cases localRun with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have initial : start=RegisterMove.before sourceWord targetWord store := Option.some.inj head
    subst start
    have projection := move_initial_projection source target different logical physical store entry saved represented scratch
    obtain ⟨posts,lastState,postLength,actualChain,actualLast,lastProjection,frame⟩ :=
      Lift.path (moveEmbedding source target different) RegisterMove.program physical
        (RegisterMove.before sourceWord targetWord store) (RegisterMove.final sourceWord)
        rest projection chain last
    have sourceValue : lastState.stk (registerSlot source)=sourceWord := by
      have part := congrArg (fun state : RegisterMove.State=>state.stk 0) lastProjection
      simpa [Lift.cfg,Lift.slots,moveEmbedding,moveSlot,
        RegisterMove.final,PDROC.BitVM.Log.TwoStack.threeStacks] using part
    have targetValue : lastState.stk (registerSlot target)=sourceWord := by
      have part := congrArg (fun state : RegisterMove.State=>state.stk 1) lastProjection
      simpa [Lift.cfg,Lift.slots,moveEmbedding,moveSlot,
        RegisterMove.final,PDROC.BitVM.Log.TwoStack.threeStacks] using part
    have scratchValue : lastState.stk 24=[] := by
      have part := congrArg (fun state : RegisterMove.State=>state.stk 2) lastProjection
      simpa [Lift.cfg,Lift.slots,moveEmbedding,moveSlot,
        RegisterMove.final,PDROC.BitVM.Log.TwoStack.threeStacks] using part
    refine ⟨after,physical::posts,lastState,rfl,rfl,actualChain,actualLast,?_,?_,scratchValue,?_,frame⟩
    · apply Lift.halt_project (moveEmbedding source target different) RegisterMove.program lastState
      rw [lastProjection]
      exact halt
    · intro reg
      by_cases isTarget : reg=target
      · subst reg
        simpa only [after,PaperProofs.Paid.Computation.State.set,Function.update_self] using targetValue
      · have logicalSame : after.register reg=logical.register reg :=
          Function.update_of_ne isTarget _ _
        rw [logicalSame]
        by_cases isSource : reg=source
        · subst reg
          exact sourceValue
        · exact (frame (registerSlot reg) (register_outside source target reg different isSource isTarget)).trans
            (represented reg)
    · simp only [List.length_cons,postLength] at length ⊢
      exact length

def literalSlot (target : Register) (index : Fin 3) : Stack :=
  if index=0 then 0 else if index=1 then registerSlot target else 31

def literalEmbedding (target : Register) : Fin 3 ↪ Stack where
  toFun := literalSlot target
  inj' := by
    intro a b equal
    have values := congrArg Fin.val equal
    have bounds := registerSlot_bounds target
    fin_cases a <;> fin_cases b <;> simp [literalSlot] at values ⊢ <;> omega

/-- Literal bytes are selected from fixed code before input, not from a
runtime mathematical RAM state. Clearing and writing them are real steps. -/
def literalMachine (target : Register) (value : Cell) : Unit → TM2.Stmt Alphabet Unit (Option Bool) :=
  Lift.machine (literalEmbedding target) (RegisterMove.literalProgram (encodeCellBits value))

theorem literal_initial_projection (target : Register)
    (logical : PaperProofs.Paid.Computation.State)
    (physical : TM2.Cfg Alphabet Unit (Option Bool)) (store : Option Bool)
    (entry : physical.l=some ()) (saved : physical.var=store)
    (represented : RegistersRepresent logical physical) (spare : physical.stk 31=[]) :
    Lift.cfg (literalEmbedding target) physical=
      RegisterMove.clearState (some ()) store (physical.stk 0) (encodeCellBits (logical.register target)) := by
  have slots : Lift.slots (literalEmbedding target) physical.stk=
      PDROC.BitVM.Log.TwoStack.threeStacks (physical.stk 0)
        (encodeCellBits (logical.register target)) [] := by
    funext index
    fin_cases index
    · rfl
    · exact represented target
    · exact spare
  change (⟨physical.l,physical.var,Lift.slots (literalEmbedding target) physical.stk⟩ :
    TM2.Cfg PDROC.BitVM.Log.TwoStack.Alphabet Unit (Option Bool))=_
  rw [entry,saved,slots]
  rfl

theorem literal_register_outside (target reg : Register) (different : reg≠target) :
    ∀ index,registerSlot reg≠literalEmbedding target index := by
  intro index
  fin_cases index
  · intro equal
    have values := congrArg Fin.val equal
    have bounds := registerSlot_bounds reg
    change (registerSlot reg).val=0 at values
    omega
  · exact fun equal=>different (registerSlot_injective equal)
  · intro equal
    have values := congrArg Fin.val equal
    have bounds := registerSlot_bounds reg
    change (registerSlot reg).val=31 at values
    omega

theorem literal_supports (target : Register) (value : Cell) :
    TM2.Supports (literalMachine target value) (Finset.univ : Finset Unit) :=
  Lift.supports (literalEmbedding target) (RegisterMove.literalProgram (encodeCellBits value)) _
    (RegisterMove.literal_supports (encodeCellBits value))

/-- Original constant instruction on all global registers, with exact
canonical Cell bytes, actual old-value clear and untouched heap/output/ROM. -/
theorem constant_instruction_runs (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (physical : TM2.Cfg Alphabet Unit (Option Bool)) (target : Register) (value : Cell) (store : Option Bool)
    (entry : physical.l=some ()) (saved : physical.var=store)
    (represented : RegistersRepresent logical physical) (spare : physical.stk 31=[]) :
    ∃ (after : PaperProofs.Paid.Computation.State)
      (run : List (TM2.Cfg Alphabet Unit (Option Bool)))
      (lastState : TM2.Cfg Alphabet Unit (Option Bool)),
      Instruction.execute input (.constant target value) logical=some after ∧
      run.head?=some physical ∧
      run.IsChain (fun a b=>TM2.step (literalMachine target value) a=some b) ∧
      run.getLast?=some lastState ∧ TM2.step (literalMachine target value) lastState=none ∧
      RegistersRepresent after lastState ∧ lastState.stk 31=[] ∧
      run.length=(encodeCellBits (logical.register target)).length+2 ∧
      ∀ other,(∀ index,other≠literalEmbedding target index)→lastState.stk other=physical.stk other := by
  let after := ({logical with pc:=logical.pc+1}).set target value
  let literal := encodeCellBits value
  let targetWord := encodeCellBits (logical.register target)
  let sourceWord := physical.stk 0
  obtain ⟨localRun,head,chain,last,halt,length,_src,_dst,_tmp⟩ :=
    RegisterMove.literal_runs literal sourceWord targetWord store
  cases localRun with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have initial : start=RegisterMove.clearState (some ()) store sourceWord targetWord := Option.some.inj head
    subst start
    have projection := literal_initial_projection target logical physical store entry saved represented spare
    obtain ⟨posts,lastState,postLength,actualChain,actualLast,lastProjection,frame⟩ :=
      Lift.path (literalEmbedding target) (RegisterMove.literalProgram literal) physical
        (RegisterMove.clearState (some ()) store sourceWord targetWord)
        (RegisterMove.clearState none none sourceWord literal) rest projection chain last
    have targetValue : lastState.stk (registerSlot target)=literal := by
      have part := congrArg (fun state : TM2.Cfg PDROC.BitVM.Log.TwoStack.Alphabet Unit (Option Bool)=>state.stk 1)
        lastProjection
      simpa [Lift.cfg,Lift.slots,literalEmbedding,literalSlot,RegisterMove.clearState,
        PDROC.BitVM.Log.TwoStack.threeStacks] using part
    have spareValue : lastState.stk 31=[] := by
      have part := congrArg (fun state : TM2.Cfg PDROC.BitVM.Log.TwoStack.Alphabet Unit (Option Bool)=>state.stk 2)
        lastProjection
      simpa [Lift.cfg,Lift.slots,literalEmbedding,literalSlot,RegisterMove.clearState,
        PDROC.BitVM.Log.TwoStack.threeStacks] using part
    refine ⟨after,physical::posts,lastState,rfl,rfl,actualChain,actualLast,?_,?_,spareValue,?_,frame⟩
    · apply Lift.halt_project (literalEmbedding target) (RegisterMove.literalProgram literal) lastState
      rw [lastProjection]
      exact halt
    · intro reg
      by_cases isTarget : reg=target
      · subst reg
        simpa only [after,PaperProofs.Paid.Computation.State.set,Function.update_self] using targetValue
      · have logicalSame : after.register reg=logical.register reg := Function.update_of_ne isTarget _ _
        rw [logicalSame]
        exact (frame (registerSlot reg) (literal_register_outside target reg isTarget)).trans (represented reg)
    · simp only [List.length_cons,postLength] at length ⊢
      exact length

end PDROC.BitVM.Kernel.RegisterGlobal
