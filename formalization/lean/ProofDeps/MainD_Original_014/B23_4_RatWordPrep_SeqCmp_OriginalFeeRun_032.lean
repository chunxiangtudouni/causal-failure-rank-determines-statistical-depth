module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeCode_030
public import B23_4_RatWordPrep_SeqCmp_RawWidth_031

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

structure Segment (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  head : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a=some b)
  last : trace.getLast?=some final
  count : trace.length≤budget

def Segment.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Segment caller before middle A) (back : Segment caller middle final B) :
    Segment caller before final (A+B) := by
  have shape : middle::back.trace.tail=back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.head
    rw [same]; rfl
  refine ⟨front.trace++back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.head]; rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count
    have b := back.count
    simp only [List.length_append,List.length_tail]
    omega

def timeCoefficient : Nat := RatInput.Complement.coefficient+
  RawGetter.coefficient*(2*RatInput.Complement.coefficient+2)^2

/-- ORIGINAL wordInput to a real third raw-field packet. The current
fee-field condition is derived from the actual original parser return;
no original caller supplies a packet, cursor, branch, width or path. -/
theorem actual (caller : Statement C) (memory : RawGetter.Store C)
    (native : RatInput.Complement.CalleeFlags) (reader : RatInput.Complement.Reader)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ trace : List (State C), ∃ final beforeRead : State C,
      trace.head?=some (entry memory native reader (wordInput E target word)) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      trace.getLast?=some final ∧ beforeRead∈trace ∧ final.l=some .done ∧ context final.var=memory.1.1 ∧
      final.stk 15=RatInput.Encoder.packet E.observationFee
        (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) ∧
      Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=Tape.mk₂
        (bothLeft (false::sign E.observationFee::true::beforeRead.stk 1)
          (numeratorDigits E.observationFee) (denominatorDigits E.observationFee)) (afterFee E target word++[true]) ∧
      final.stk 7=[] ∧ final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
      final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[] ∧
      trace.length≤timeCoefficient*((wordInput E target word).length+1)^16 := by
  obtain ⟨cTrace,cFinal,cParsed,cFirst,cChain,cLast,_cMember,cActive,cContext,cContents,cTape,cTime,cBounds,_cNodes,_cProper⟩ :=
    RatInput.Complement.actual_original_complement_uniform memory native reader E target word
  have cPath := front_path caller cTrace _ cFinal cFirst cChain cLast cActive
  have source : cFinal.stk 15=RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne []) := by
    rw [cContents]
    rfl
  have scratch : cFinal.stk 7=[] := by rw [cContents]; rfl
  have right : ListBlank.mk (cFinal.stk 0)=ListBlank.mk
      (encodeDatum (.rational E.observationFee)++afterFee E target word++[true]) := by
    have actualRight := congrArg Tape.right₀ cTape
    simp only [Tape.mk₂,Tape.mk'_right₀] at actualRight
    rw [after_prior_fee] at actualRight
    rw [cContents]
    exact actualRight
  let rawMemory := (rawIso C).symm cFinal.var
  obtain ⟨rTrace,rFinal,rParsed,rFacts⟩ := RawGetter.actual_polynomial_current
    cFinal.stk rawMemory E.observationFee (afterFee E target word) right
  have rPath := read_path caller rTrace _ rFinal rFacts.first rFacts.chain rFacts.last rFacts.active
  let front : Segment caller (entry memory native reader (wordInput E target word)) (frontCfg cFinal)
      (RatInput.Complement.coefficient*((wordInput E target word).length+1)^8) :=
    ⟨cTrace.map frontCfg,cPath.1,cPath.2.1,cPath.2.2,by simpa only [List.length_map] using cTime⟩
  let back : Segment caller (frontCfg cFinal) (readCfg rFinal)
      (RawGetter.coefficient*(RawGetter.inputScale cFinal.stk E.observationFee)^2) :=
    ⟨rTrace.map readCfg,rPath.1.trans (congrArg some (shared cFinal cActive)),rPath.2.1,rPath.2.2,
      by simpa only [List.length_map,RawGetter.degree] using rFacts.time⟩
  let whole := front.append back
  have finalContext : context (readCfg rFinal).var=context (frontCfg cFinal).var :=
    congrArg (fun v : RatInput.Complement.Store C => v.1.1.1.1.1) rFacts.context_eq
  have originalContext : context (frontCfg cFinal).var=memory.1.1 :=
    congrArg (fun v : RawGetter.Store C => v.1.1) cContext
  have rawFinal := RawGetter.Public.final_fields rFacts
  have fields : ∀ slot, ¬RawGetter.Work slot → rFinal.stk slot=cFinal.stk slot := rawFinal.2.2.2.2
  have feeOutput : (readCfg rFinal).stk 15=RatInput.Encoder.packet E.observationFee
      (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) := by
    change rFinal.stk 15=_
    rw [rawFinal.1,source]
  have finalTape : Tape.mk' (ListBlank.mk ((readCfg rFinal).stk 1)) (ListBlank.mk ((readCfg rFinal).stk 0))=Tape.mk₂
      (bothLeft (false::sign E.observationFee::true::(frontCfg cFinal).stk 1)
        (numeratorDigits E.observationFee) (denominatorDigits E.observationFee)) (afterFee E target word++[true]) := by
    change Tape.mk' (ListBlank.mk (rFinal.stk 1)) (ListBlank.mk (rFinal.stk 0))=_
    rw [rawFinal.2.2.1,rawFinal.2.2.2.1]
    exact rFacts.parserTape
  have base : 1 ≤ (wordInput E target word).length+1 := by omega
  have one : 1≤((wordInput E target word).length+1)^8 := Nat.pow_le_pow_left base 8
  have mass := (cBounds cFinal (List.mem_of_getLast? cLast)).2
  have scale := RawGetter.inputScale_le_mass cFinal.stk E.observationFee (afterFee E target word) right
  have enlarged : RawGetter.inputScale cFinal.stk E.observationFee≤
      (2*RatInput.Complement.coefficient+2)*((wordInput E target word).length+1)^8 := by
    calc
      _ ≤ 2*(RatInput.occupied cFinal.stk+1) := scale
      _ ≤ 2*(RatInput.Complement.coefficient*((wordInput E target word).length+1)^8+1) :=
        Nat.mul_le_mul_left 2 (Nat.add_le_add_right mass 1)
      _ ≤ 2*(RatInput.Complement.coefficient*((wordInput E target word).length+1)^8+
          ((wordInput E target word).length+1)^8) := Nat.mul_le_mul_left 2 (Nat.add_le_add_left one _)
      _ = _ := by ring
  have power := Nat.mul_le_mul_left RawGetter.coefficient (Nat.pow_le_pow_left enlarged 2)
  have rawCap : RawGetter.coefficient*(RawGetter.inputScale cFinal.stk E.observationFee)^2≤
      RawGetter.coefficient*(2*RatInput.Complement.coefficient+2)^2*((wordInput E target word).length+1)^16 := by
    simpa only [mul_pow,←pow_mul,Nat.mul_assoc] using power
  have degree : ((wordInput E target word).length+1)^8≤((wordInput E target word).length+1)^16 :=
    Nat.pow_le_pow_right base (by decide : (8:Nat)≤16)
  refine ⟨whole.trace,readCfg rFinal,frontCfg cFinal,whole.head,whole.chain,whole.last,?_,?_,
    finalContext.trans originalContext,feeOutput,finalTape,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact List.mem_append_left _ (List.mem_of_getLast? front.last)
  · dsimp only [readCfg,StoreIso.configuration,LabelMap.configuration]
    rw [rFacts.active]
    rfl
  · exact rawFinal.2.1.trans scratch
  · exact (fields 3 (by decide)).trans (by rw [cContents]; rfl)
  · exact (fields 4 (by decide)).trans (by rw [cContents]; rfl)
  · exact (fields 5 (by decide)).trans (by rw [cContents]; rfl)
  · exact (fields 6 (by decide)).trans (by rw [cContents]; rfl)
  · exact (fields 12 (by decide)).trans (by rw [cContents]; rfl)
  · exact (fields 13 (by decide)).trans (by rw [cContents]; rfl)
  · exact (fields 14 (by decide)).trans (by rw [cContents]; rfl)
  · calc
      whole.trace.length ≤ RatInput.Complement.coefficient*((wordInput E target word).length+1)^8+
          RawGetter.coefficient*(RawGetter.inputScale cFinal.stk E.observationFee)^2 := whole.count
      _ ≤ RatInput.Complement.coefficient*((wordInput E target word).length+1)^16+
          RawGetter.coefficient*(2*RatInput.Complement.coefficient+2)^2*((wordInput E target word).length+1)^16 :=
        Nat.add_le_add (Nat.mul_le_mul_left RatInput.Complement.coefficient degree) rawCap
      _ = _ := by dsimp only [timeCoefficient]; ring

end B23_4_RatWordPrep.OriginalFee
