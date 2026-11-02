module

public import Paid.PDROC_BitVM_Kernel_NatMarshal_001
public import Paid.PDROC_BitVM_Kernel_Register_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Kernel.NatMarshalGlobal

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev State := TM2.Cfg RegisterGlobal.Alphabet NatMarshal.Label NatMarshal.Store

/-- One fixed register source, the real native-right stack and its scratch.
Left/right source operands may be the same register: use this embedding
twice, first for the right operand and then for the left operand. -/
def embedding (source : Register) : Fin 3 ↪ RegisterGlobal.Stack where
  toFun := fun index=>if index=0 then registerSlot source else if index=1 then 0 else 24
  inj' := by
    intro a b same
    have values := congrArg Fin.val same
    have bounds := registerSlot_bounds source
    fin_cases a <;> fin_cases b <;> simp at values ⊢ <;> omega

def machine (source : Register) : NatMarshal.Label →
    TM2.Stmt RegisterGlobal.Alphabet NatMarshal.Label NatMarshal.Store :=
  Lift.machine (embedding source) NatMarshal.program

theorem outside_register (source reg : Register) (different : reg≠source) :
    ∀ index,registerSlot reg≠embedding source index := by
  intro index
  fin_cases index
  · exact fun same=>different (registerSlot_injective same)
  · intro same
    have value := congrArg Fin.val same
    have bounds := registerSlot_bounds reg
    change (registerSlot reg).val=0 at value
    omega
  · intro same
    have value := congrArg Fin.val same
    have bounds := registerSlot_bounds reg
    change (registerSlot reg).val=24 at value
    omega

theorem initial_projection (source : Register) (value : ℕ) (target : List Bool)
    (physical : State) (store : Option Bool)
    (entry : physical.l=some 0) (saved : physical.var=(store,()))
    (sourceWord : physical.stk (registerSlot source)=encodeCellBits (.natural value))
    (targetWord : physical.stk 0=target) (scratch : physical.stk 24=[]) :
    Lift.cfg (embedding source) physical=NatMarshal.before (encodeNatBits value) target store := by
  have slots : Lift.slots (embedding source) physical.stk=
      PDROC.BitVM.Log.TwoStack.threeStacks (false::encodeNatBits value) target [] := by
    funext index
    fin_cases index
    · exact sourceWord
    · exact targetWord
    · exact scratch
  change (⟨physical.l,physical.var,Lift.slots (embedding source) physical.stk⟩ : NatMarshal.State)=_
  rw [entry,saved,slots]
  rfl

/-- A genuine source-preserving read of an original natural register into
the native work tape. No assumption supplies an encoded operand tape:
only the actual register representation and empty scratch are required. -/
theorem register_runs (logical : PaperProofs.Paid.Computation.State) (source : Register)
    (value : ℕ) (target : List Bool) (physical : State) (store : Option Bool)
    (entry : physical.l=some 0) (saved : physical.var=(store,()))
    (represented : RegistersRepresent logical physical)
    (natural : logical.register source=.natural value)
    (targetWord : physical.stk 0=target) (scratch : physical.stk 24=[]) :
    ∃ (run : List State) (lastState : State),
      run.head?=some physical ∧ run.IsChain (fun a b=>TM2.step (machine source) a=some b) ∧
      run.getLast?=some lastState ∧ TM2.step (machine source) lastState=none ∧
      lastState.l=none ∧ lastState.var=(none,()) ∧
      RegistersRepresent logical lastState ∧ lastState.stk 0=encodeNatBits value++target ∧
      lastState.stk 24=[] ∧ run.length=2*(encodeNatBits value).length+5 ∧
      ∀ other,(∀ index,other≠embedding source index)→lastState.stk other=physical.stk other := by
  have sourceWord : physical.stk (registerSlot source)=encodeCellBits (.natural value) := by
    rw [represented source,natural]
  have projection := initial_projection source value target physical store entry saved sourceWord targetWord scratch
  obtain ⟨localRun,head,chain,last,halt,length,_source,_target,_scratch⟩ :=
    NatMarshal.marshal_runs (encodeNatBits value) target store
  cases localRun with
  | nil => simp only [List.head?_nil,reduceCtorEq] at head
  | cons start rest =>
    have initial : start=NatMarshal.before (encodeNatBits value) target store := Option.some.inj head
    subst start
    obtain ⟨posts,lastState,postLength,actualChain,actualLast,lastProjection,frame⟩ :=
      Lift.path (embedding source) NatMarshal.program physical
        (NatMarshal.before (encodeNatBits value) target store)
        (NatMarshal.final (encodeNatBits value) target) rest projection chain last
    have sourceFinal : lastState.stk (registerSlot source)=encodeCellBits (.natural value) := by
      have part := congrArg (fun state : NatMarshal.State=>state.stk 0) lastProjection
      simpa [Lift.cfg,Lift.slots,embedding,NatMarshal.final,encodeCellBits,
        PDROC.BitVM.Log.TwoStack.threeStacks] using part
    have targetFinal : lastState.stk 0=encodeNatBits value++target := by
      have part := congrArg (fun state : NatMarshal.State=>state.stk 1) lastProjection
      simpa [Lift.cfg,Lift.slots,embedding,NatMarshal.final,
        PDROC.BitVM.Log.TwoStack.threeStacks] using part
    have scratchFinal : lastState.stk 24=[] := by
      have part := congrArg (fun state : NatMarshal.State=>state.stk 2) lastProjection
      simpa [Lift.cfg,Lift.slots,embedding,NatMarshal.final,
        PDROC.BitVM.Log.TwoStack.threeStacks] using part
    have labelFinal : lastState.l=none := congrArg TM2.Cfg.l lastProjection
    have storeFinal : lastState.var=(none,()) := congrArg TM2.Cfg.var lastProjection
    refine ⟨physical::posts,lastState,rfl,actualChain,actualLast,?_,labelFinal,storeFinal,
      ?_,targetFinal,scratchFinal,?_,frame⟩
    · apply Lift.halt_project (embedding source) NatMarshal.program lastState
      rw [lastProjection]
      exact halt
    · intro reg
      by_cases same : reg=source
      · subst reg
        rw [natural]
        exact sourceFinal
      · exact (frame (registerSlot reg) (outside_register source reg same)).trans (represented reg)
    · simp only [List.length_cons,postLength] at length ⊢
      exact length

theorem supports (source : Register) :
    TM2.Supports (machine source) (Finset.univ : Finset NatMarshal.Label) :=
  Lift.supports (embedding source) NatMarshal.program _ NatMarshal.supports

end PDROC.BitVM.Kernel.NatMarshalGlobal
