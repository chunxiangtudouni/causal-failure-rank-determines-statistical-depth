module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeResources_035

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalFee

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PA17TMRatArithmeticParse002

variable {C : Type*}

def space (length : Nat) : Nat := length+16*(timeCoefficient*(length+1)^16)
def coefficient : Nat := 64*(1+16*timeCoefficient+32)
def degree : Nat := 16

theorem coefficient_pos : 0<coefficient := by unfold coefficient; omega
theorem degree_eq_sixteen : degree=16 := rfl

theorem resource_envelope (length : Nat) :
    timeCoefficient*(length+1)^16≤coefficient*(length+1)^degree ∧
    16*space length≤coefficient*(length+1)^degree ∧
    space length+16≤coefficient*(length+1)^degree ∧
    32*(space length+17)≤coefficient*(length+1)^degree := by
  have base : 1≤length+1 := by omega
  have linear : length+1≤(length+1)^16 := by
    have h := Nat.pow_le_pow_right base (by decide : (1:Nat)≤16)
    simpa only [pow_one] using h
  have positive : 1≤(length+1)^16 := Nat.pow_le_pow_left base 16
  have bound : space length≤(1+16*timeCoefficient)*(length+1)^16 := by
    dsimp only [space]
    nlinarith only [linear]
  have coefficientBound : timeCoefficient≤coefficient := by unfold coefficient; omega
  refine ⟨Nat.mul_le_mul_right _ coefficientBound,?_,?_,?_⟩
  all_goals dsimp only [coefficient,degree]
  all_goals nlinarith only [bound,positive]

structure Facts (source : Label → Statement C) (memory : RawGetter.Store C)
    (native : RatInput.Complement.CalleeFlags) (reader : RatInput.Complement.Reader)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (trace : List (State C)) (final beforeRead : State C) : Prop where
  first : trace.head?=some (entry memory native reader (wordInput E target word))
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final
  read_member : beforeRead∈trace
  active : final.l=some .done
  context_eq : context final.var=memory.1.1
  packet : final.stk 15=RatInput.Encoder.packet E.observationFee
    (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne []))
  cursor : Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=Tape.mk₂
    (bothLeft (false::sign E.observationFee::true::beforeRead.stk 1)
      (numeratorDigits E.observationFee) (denominatorDigits E.observationFee)) (afterFee E target word++[true])
  owned : final.stk 7=[] ∧ final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
    final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[]
  time : trace.length≤coefficient*((wordInput E target word).length+1)^degree
  boundaries : ∀ current∈trace,context current.var=memory.1.1 ∧
    (∀ slot,(current.stk slot).length≤coefficient*((wordInput E target word).length+1)^degree) ∧
    RatInput.occupied current.stk≤coefficient*((wordInput E target word).length+1)^degree ∧
    ∀ slot,¬Work slot→current.stk slot=[]
  proper : ∀ current∈trace.dropLast,current.l≠some .done ∧
    ∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (source point) current.var current.stk,
        context node.1=memory.1.1 ∧
        (∀ slot,(node.2 slot).length≤coefficient*((wordInput E target word).length+1)^degree) ∧
        ∀ slot,¬Work slot→node.2 slot=[]) ∧
      ScannerStatement.clock (source point) current.var current.stk≤coefficient*((wordInput E target word).length+1)^degree

theorem actual_polynomial (memory : RawGetter.Store C) (native : RatInput.Complement.CalleeFlags)
    (reader : RatInput.Complement.Reader) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ trace final beforeRead,Facts (program .halt) memory native reader E target word trace final beforeRead := by
  obtain ⟨trace,final,beforeRead,first,chain,last,member,active,finalContext,packet,cursor,s7,s3,s4,s5,s6,s12,s13,s14,count⟩ :=
    actual .halt memory native reader E target word
  let bits := wordInput E target word
  let before := entry memory native reader bits
  have frames : ∀ slot,¬Work slot→before.stk slot=[] := by
    intro slot untouched
    have notZero : slot≠0 := by intro same; subst slot; exact untouched (by decide)
    change (entry memory native reader bits).stk slot=[]
    rw [entry_slots]
    simp only [notZero,ite_false]
  have initialBound : ∀ slot,(before.stk slot).length≤bits.length := by
    intro slot
    have bound := RatInput.Encoder.point_mass before.stk slot
    rw [entry_mass] at bound
    exact bound
  have bounds := trace_resources trace before (fun _ => []) bits.length first chain initialBound frames
  have contexts := trace_context trace before first chain
  have bounded : ∀ current∈trace,∀ slot,(current.stk slot).length≤space bits.length := by
    intro current present slot
    exact ((bounds current present).1 slot).trans (Nat.add_le_add_left (Nat.mul_le_mul_left 16 count) _)
  have caps := resource_envelope bits.length
  have proper := NativeMulLink.no_early_halt_port (program .halt) .done rfl trace final chain last active
  refine ⟨trace,final,beforeRead,⟨first,chain,last,member,active,finalContext,packet,cursor,
    ⟨s7,s3,s4,s5,s6,s12,s13,s14⟩,count.trans caps.1,?_,?_⟩⟩
  · intro current present
    refine ⟨contexts current present,?_,?_,(bounds current present).2⟩
    · intro slot
      exact (bounded current present slot).trans
        ((Nat.le_mul_of_pos_left _ (by decide : 0<16)).trans caps.2.1)
    · exact (RatInput.Encoder.occupied_bound current.stk _ (bounded current present)).trans caps.2.1
  · intro current present
    refine ⟨proper current present,?_⟩
    intro point selected
    have internal := internal_resources current point _ (bounded current (List.mem_of_mem_dropLast present))
    refine ⟨?_,internal.2.trans caps.2.2.2⟩
    intro node inside
    exact ⟨((internal.1 node inside).1).trans (contexts current (List.mem_of_mem_dropLast present)),
      fun slot => ((internal.1 node inside).2.1 slot).trans caps.2.2.1,
      fun slot untouched => ((internal.1 node inside).2.2 slot untouched).trans
        ((bounds current (List.mem_of_mem_dropLast present)).2 slot untouched)⟩

end B23_4_RatWordPrep.OriginalFee
