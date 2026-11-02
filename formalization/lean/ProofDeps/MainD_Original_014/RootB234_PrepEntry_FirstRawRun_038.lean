module

public import RootB234_PrepEntry_FirstRawPrefix_037

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.FirstRaw

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PA17TMRatArithmeticParse002

variable {C : Type*} {I : Instance}

def time (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  prefixTime input contract budget+RawGetter.time (firstValue input budget)

/-- The actual original preparation producer, including N=0, exports
the first original Rat on13 and the preceding original natural on14.
The original numeric caller supplies no prefix, width or parser witness. -/
theorem actual (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C) (suffix left : List Bool),
      trace.head?=some (entry context background (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      final.stk 14=NatField.packet (lastNatural input contract) (background 14) ∧
      final.stk 13=RatInput.Encoder.packet (firstValue input budget) (background 13) ∧
      final.stk 7=background 7 ∧
      NatPrefix.tape final.stk=Tape.mk₂ left (suffix++[true]) ∧
      callerContext final.var=context ∧
      (∀ slot,¬Work slot→final.stk slot=background slot) ∧
      trace.length≤time input contract budget := by
  obtain ⟨nRun,nFinal,suffix,nFirst,nChain,nLast,nActive,nPacket,nTape,nFrames,nTime⟩:=
    actual_prefix .halt context background input contract budget
  let rStart : RawGetter.State (RawContext C):=⟨some .boot,(rawIso C).symm nFinal.var,
    StackIso.slots rationalRoles.symm nFinal.stk⟩
  have right : ListBlank.mk (rStart.stk 0)=ListBlank.mk
      (encodeDatum (.rational (firstValue input budget))++suffix++[true]) := by
    change ListBlank.mk (nFinal.stk 0)=_
    simpa only [NatPrefix.tape,Tape.mk₂,Tape.mk'_right₀] using congrArg Tape.right₀ nTape
  obtain ⟨rRun,rFinal,parsed,rFirst,rChain,rLast,_parsedMember,rActive,_rContext,rContents,rTape,rScratch,_rTarget,rTime⟩:=
    RawGetter.actual_current_field .halt rStart.stk rStart.var (firstValue input budget) suffix right
  have rPath:=rational_path (.halt : Statement C) rRun rStart rFinal rFirst rChain rLast rActive
  have shared : rationalCfg rStart=nFinal := by
    cases nFinal with
    | mk point memory contents =>
      change point=some (.rational .boot) at nActive
      subst point
      change (⟨some (.rational .boot),rawIso C ((rawIso C).symm memory),
        StackIso.slots rationalRoles (StackIso.slots rationalRoles.symm contents)⟩ : State C)=_
      rw [Equiv.apply_symm_apply]
      congr 1
      funext slot
      fin_cases slot <;> rfl
  let frontSegment : Segment (.halt : Statement C)
      (entry context background (preparationInput input contract budget)) nFinal (prefixTime input contract budget):=
    ⟨nRun,nFirst,nChain,nLast,nTime⟩
  let rational : Segment (.halt : Statement C) nFinal (rationalCfg rFinal)
      (RawGetter.time (firstValue input budget)):=
    ⟨rRun.map rationalCfg,rPath.1.trans (congrArg some shared),rPath.2.1,rPath.2.2,
      by simpa only [List.length_map] using rTime⟩
  let whole:=frontSegment.append rational
  have ratPacket : (rationalCfg rFinal).stk 13=
      RatInput.Encoder.packet (firstValue input budget) (background 13) := by
    change rFinal.stk 15=_
    rw [rContents]
    change RatInput.Encoder.packet (firstValue input budget) (nFinal.stk 13)=_
    rw [nFrames 13 (by decide) (by decide) (by decide)]
  have naturalFrame : rFinal.stk 14=rStart.stk 14 :=
    trace_untouched (RawGetter.program .halt) RawWork raw_writes rRun rStart rFirst rChain
      14 (by decide) rFinal (List.mem_of_getLast? rLast)
  have natPacket : (rationalCfg rFinal).stk 14=NatField.packet (lastNatural input contract) (background 14) := by
    change rFinal.stk 14=_
    rw [naturalFrame]
    exact nPacket
  have scratch : (rationalCfg rFinal).stk 7=background 7 := by
    change rFinal.stk 7=_
    rw [rContents]
    change parsed.stk 7=background 7
    rw [rScratch]
    exact nFrames 7 (by decide) (by decide) (by decide)
  have sourceTape : NatPrefix.tape (rationalCfg rFinal).stk=NatPrefix.tape parsed.stk := by
    change Tape.mk' (ListBlank.mk (rFinal.stk 1)) (ListBlank.mk (rFinal.stk 0))=_
    rw [rContents]
    rfl
  have fullTape : NatPrefix.tape (rationalCfg rFinal).stk=Tape.mk₂
      (bothLeft (false::sign (firstValue input budget)::true::rStart.stk 1)
        (numeratorDigits (firstValue input budget)) (denominatorDigits (firstValue input budget))) (suffix++[true]) := by
    rw [sourceTape]
    exact rTape
  have contexts:=trace_context whole.trace _ whole.first whole.chain
  have outside : ∀ slot,¬Work slot→(rationalCfg rFinal).stk slot=background slot := by
    intro slot untouched
    have frame:=trace_untouched (program .halt) Work program_writes whole.trace _ whole.first whole.chain
      slot untouched (rationalCfg rFinal) (List.mem_of_getLast? whole.last)
    rw [frame,entry_slots]
    have notZero : slot≠0 := by intro same; subst slot; exact untouched (by decide)
    have notOne : slot≠1 := by intro same; subst slot; exact untouched (by decide)
    simp only [notZero,notOne,ite_false]
  refine ⟨whole.trace,rationalCfg rFinal,suffix,_,whole.first,whole.chain,whole.last,?_,natPacket,
    ratPacket,scratch,fullTape,?_,outside,whole.count⟩
  · change Option.map rationalLabel rFinal.l=some .done
    rw [rActive]; rfl
  · exact contexts _ (List.mem_of_getLast? whole.last)

end RootB234.PrepEntry.FirstRaw
