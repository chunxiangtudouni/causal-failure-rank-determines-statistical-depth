module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludeLookahead_059

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalPrelude

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM PA17TMRatArithmeticParse002

variable {C : Type*}

def timeCoefficient : Nat := 2048+OriginalFee.coefficient

/-- ORIGINAL input -> physical alphabet8 and prior/complement/fee15 in
one source and one actual trace. The lookahead/rewind is paid and the fee
auxiliary block was allocated at the literal entry, never reset at a join. -/
theorem actual (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (run : List (State C)) (final beforeRead : State C),
      run.head?=some (entry context (wordInput E target word)) ∧
      run.IsChain (fun a b => TM2.step (program caller) a=some b) ∧
      run.getLast?=some final ∧ beforeRead∈run ∧ final.l=some .done ∧
      OriginalFee.context (feeMemory final.var)=context ∧
      final.stk 8=NatField.packet E.alphabetSize [] ∧
      final.stk 15=RatInput.Encoder.packet E.observationFee
        (RatInput.Encoder.packet (1-E.priorOne) (RatInput.Encoder.packet E.priorOne [])) ∧
      Tape.mk' (ListBlank.mk (final.stk 1)) (ListBlank.mk (final.stk 0))=Tape.mk₂
        (bothLeft (false::sign E.observationFee::true::beforeRead.stk 1)
          (numeratorDigits E.observationFee) (denominatorDigits E.observationFee))
        (OriginalFee.afterFee E target word++[true]) ∧
      (final.stk 7=[] ∧ final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
        final.stk 12=[] ∧ final.stk 13=[] ∧ final.stk 14=[]) ∧
      (∀ slot,slot=2 ∨ slot=9 ∨ slot=10 ∨ slot=11→final.stk slot=[]) ∧
      run.length ≤ timeCoefficient*((wordInput E target word).length+1)^16 := by
  let bits:=wordInput E target word
  let cache:=NatField.packet E.alphabetSize []
  obtain ⟨lRun,lFinal,lFirst,lChain,lLast,lActive,lMemory,lBank,lCount⟩:=actual_lookahead caller context E target word
  let registers:=extra lFinal.var
  let beforeFee:=Frame.configuration 8 cache (OriginalFee.entry (rawMemory context) default default bits)
  have shared : feeCfg registers beforeFee=lFinal := by
    rcases lFinal with ⟨position,memory,contents⟩
    change position=some (.fee default) at lActive
    subst position
    change (⟨some (.fee default),feeIso C (extra memory,beforeFee.var),beforeFee.stk⟩ : State C)=
      ⟨some (.fee default),memory,contents⟩
    have varEq : beforeFee.var=feeMemory memory := by
      change (OriginalFee.entry (rawMemory context) default default bits).var=feeMemory memory
      rw [feeMemory_entry,lMemory]
    rw [varEq,fee_split]
    exact congrArg (fun bank : RatInput.Stack → List Bool => (⟨some (Label.fee default),memory,bank⟩ : State C)) lBank.symm
  obtain ⟨original,oFinal,oRead,facts,fFirst,fChain,fLast,_fCache,_fPacket,_fClock,_fCharge⟩:=
    OriginalFee.actual_cached8 (rawMemory context) default default E target word cache
  let cachedRun:=original.map (Frame.configuration 8 cache)
  let cachedFinal:=Frame.configuration 8 cache oFinal
  let read:=feeCfg registers (Frame.configuration 8 cache oRead)
  have fPath:=fee_path caller registers cachedRun beforeFee cachedFinal fFirst fChain fLast facts.active
  let front : Segment caller (entry context bits) lFinal (2048*(bits.length+1)^2):=
    ⟨lRun,lFirst,lChain,lLast,lCount⟩
  let back : Segment caller lFinal (feeCfg registers cachedFinal) (OriginalFee.coefficient*(bits.length+1)^16):=
    ⟨cachedRun.map (feeCfg registers),fPath.1.trans (congrArg some shared),fPath.2.1,fPath.2.2,
      by simpa only [cachedRun,List.length_map,OriginalFee.degree,bits] using facts.time⟩
  let whole:=front.append back
  have memberBack : read∈back.trace := by
    apply List.mem_map.mpr
    refine ⟨Frame.configuration 8 cache oRead,?_,rfl⟩
    exact List.mem_map.mpr ⟨oRead,facts.read_member,rfl⟩
  have member : read∈whole.trace := by
    have shape : lFinal::back.trace.tail=back.trace := by
      obtain ⟨rest,same⟩:=List.head?_eq_some_iff.mp back.head
      rw [same]
      rfl
    rw [←shape] at memberBack
    change read∈front.trace++back.trace.tail
    rcases List.mem_cons.mp memberBack with same | later
    · rw [same]
      exact List.mem_append_left _ (List.mem_of_getLast? front.last)
    · exact List.mem_append_right _ later
  have fields : ∀ slot,slot≠8→(feeCfg registers cachedFinal).stk slot=oFinal.stk slot := by
    intro slot different
    change Function.update oFinal.stk 8 cache slot=oFinal.stk slot
    exact Function.update_of_ne different _ _
  have owned:=facts.owned
  have finalFrame:=(facts.boundaries oFinal (List.mem_of_getLast? facts.last)).2.2.2
  refine ⟨whole.trace,feeCfg registers cachedFinal,read,whole.head,whole.chain,whole.last,member,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · change oFinal.l.map feeLabel=some .done
    rw [facts.active]
    rfl
  · exact facts.context_eq
  · change Function.update oFinal.stk (8 : RatInput.Stack) cache 8=cache
    exact Function.update_self _ _ _
  · rw [fields 15 (by decide)]
    exact facts.packet
  · rw [fields 1 (by decide),fields 0 (by decide)]
    change Tape.mk' (ListBlank.mk (oFinal.stk 1)) (ListBlank.mk (oFinal.stk 0))=Tape.mk₂
      (bothLeft (false::sign E.observationFee::true::Function.update oRead.stk 8 cache 1)
        (numeratorDigits E.observationFee) (denominatorDigits E.observationFee))
      (OriginalFee.afterFee E target word++[true])
    rw [Function.update_of_ne (by decide : (1:RatInput.Stack)≠8)]
    exact facts.cursor
  · rw [fields 7 (by decide),fields 3 (by decide),fields 4 (by decide),fields 5 (by decide),
      fields 6 (by decide),fields 12 (by decide),fields 13 (by decide),fields 14 (by decide)]
    exact owned
  · intro slot selected
    rcases selected with rfl | rfl | rfl | rfl
    all_goals rw [fields _ (by decide)]
    all_goals exact finalFrame _ (by decide)
  · have base : 1 ≤ bits.length+1 := by omega
    have powers : (bits.length+1)^2 ≤ (bits.length+1)^16 := Nat.pow_le_pow_right base (by decide : (2:Nat) ≤ 16)
    have count:=whole.count
    have small:=Nat.mul_le_mul_left 2048 powers
    change whole.trace.length ≤ timeCoefficient*(bits.length+1)^16
    dsimp only [timeCoefficient]
    nlinarith only [count,small]

end B23_4_RatWordPrep.OriginalPrelude
