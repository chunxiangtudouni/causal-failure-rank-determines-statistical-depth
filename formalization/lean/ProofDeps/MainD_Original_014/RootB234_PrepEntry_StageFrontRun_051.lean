module

public import RootB234_PrepEntry_StageFrontPrefix_050

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageFront

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

variable {C : Type*} {I : Instance}

def afterFee (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : List Bool :=
  if positive : 0<I.stageCount then
    (FirstRaw.channelValues (input.experiment ⟨0,positive⟩)).flatMap (fun value => encodeDatum (.rational value))++
      (FirstRaw.afterFirstExperiment input contract budget).flatMap encodeDatum
  else []

def feeOutput (input : StatisticalInput I) (old : List Bool) : List Bool :=
  if positive : 0<I.stageCount then RatInput.Encoder.packet (input.experiment ⟨0,positive⟩).observationFee old else old

def time (input : StatisticalInput I) (contract : Contract I) (budget : Rat) : Nat :=
  prefixTime input contract budget+2+
    if positive : 0<I.stageCount then RawGetter.time (input.experiment ⟨0,positive⟩).observationFee else 0

def Work (slot : RatInput.Stack) : Prop := slot=0 ∨ slot=1 ∨ slot=7 ∨ slot=12 ∨ slot=13 ∨ slot=14
instance (slot : RatInput.Stack) : Decidable (Work slot) := by unfold Work; infer_instance

theorem old_work (slot : RatInput.Stack) (safe : ¬Work slot) : ¬FirstRaw.Work slot := by
  simp only [Work,FirstRaw.Work] at safe ⊢
  tauto

/-- Fixed original-input source, with its actual canonical-N guard.
No positive-stage condition is added to the original caller. The zero
case stops at EOF; the positive case physically reads observationFee. -/
theorem actual (context : C) (background : RatInput.Stack → List Bool)
    (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry context background (preparationInput input contract budget)) ∧
      trace.IsChain (fun a b => TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some final ∧ final.l=some .done ∧
      final.stk 14=NatField.packet (FirstRaw.lastNatural input contract) (background 14) ∧
      final.stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) (background 13) ∧
      final.stk 12=feeOutput input (background 12) ∧ final.stk 7=background 7 ∧
      ListBlank.mk (final.stk 0)=ListBlank.mk (afterFee input contract budget++[true]) ∧
      callerContext final.var=context ∧
      (∀ slot,¬Work slot→final.stk slot=background slot) ∧
      trace.length≤time input contract budget ∧ final.var.2.2=decide (I.stageCount≠0) := by
  obtain ⟨nRun,nFinal,left,nFirst,nChain,nLast,nActive,nFlag,nNatural,nPrior,nScratch,nTape,nContext,nFrames,nTime⟩:=
    actual_prefix .halt context background input contract budget
  let front : Segment (.halt : Statement C) (entry context background (preparationInput input contract budget))
      nFinal (prefixTime input contract budget):=⟨nRun,nFirst,nChain,nLast,nTime⟩
  by_cases positive : 0<I.stageCount
  · have nonzero : I.stageCount≠0 := by omega
    let rStart : RawGetter.State (FirstRaw.RawContext C):=⟨some .boot,(FirstRaw.rawIso C).symm nFinal.var,
      StackIso.slots feeRoles.symm nFinal.stk⟩
    have shared : feeCfg rStart=(⟨some (.fee .boot),nFinal.var,nFinal.stk⟩ : State C) := by
      change (⟨some (.fee .boot),FirstRaw.rawIso C ((FirstRaw.rawIso C).symm nFinal.var),
        StackIso.slots feeRoles (StackIso.slots feeRoles.symm nFinal.stk)⟩ : State C)=_
      rw [Equiv.apply_symm_apply]
      congr 1
      funext slot
      fin_cases slot <;> rfl
    have selected : TM2.step (program .halt) nFinal=some (feeCfg rStart) := by
      cases nFinal with
      | mk point memory contents =>
        change point=some .select at nActive
        subst point
        rw [shared,select_step]
        change memory.2.2=decide (I.stageCount≠0) at nFlag
        rw [nFlag]
        simp [nonzero]
    let selectSegment : Segment (.halt : Statement C) nFinal (feeCfg rStart) 2:=
      ⟨[nFinal,feeCfg rStart],rfl,List.isChain_cons_cons.mpr ⟨selected,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
    have right : ListBlank.mk (rStart.stk 0)=ListBlank.mk
        (encodeDatum (.rational (input.experiment ⟨0,positive⟩).observationFee)++afterFee input contract budget++[true]) := by
      change ListBlank.mk (nFinal.stk 0)=_
      have current:=congrArg Tape.right₀ nTape
      rw [FirstRaw.wireSuffix_positive input contract budget positive] at current
      simpa only [NatPrefix.tape,Tape.mk₂,Tape.mk'_right₀,afterFee,dite_eq_left positive,List.append_assoc] using current
    obtain ⟨rRun,rFinal,parsed,rFirst,rChain,rLast,_parsed,rActive,rContext,rContents,rTape,rScratch,_rTarget,rTime⟩:=
      RawGetter.actual_current_field .halt rStart.stk rStart.var
        (input.experiment ⟨0,positive⟩).observationFee (afterFee input contract budget) right
    have rPath:=fee_path (.halt : Statement C) rRun rStart rFinal rFirst rChain rLast rActive
    let feeSegment : Segment (.halt : Statement C) (feeCfg rStart) (feeCfg rFinal)
        (RawGetter.time (input.experiment ⟨0,positive⟩).observationFee):=
      ⟨rRun.map feeCfg,rPath.1,rPath.2.1,rPath.2.2,by simpa only [List.length_map] using rTime⟩
    let whole:=(front.append selectSegment).append feeSegment
    have rawFrame (slot : RatInput.Stack) (safe : ¬FirstRaw.RawWork slot) : rFinal.stk slot=rStart.stk slot :=
      FirstRaw.trace_untouched (RawGetter.program .halt) FirstRaw.RawWork FirstRaw.raw_writes rRun rStart
        rFirst rChain slot safe rFinal (List.mem_of_getLast? rLast)
    have natural : (feeCfg rFinal).stk 14=NatField.packet (FirstRaw.lastNatural input contract) (background 14) := by
      change rFinal.stk 14=_
      rw [rawFrame 14 (by decide)]
      exact nNatural
    have prior : (feeCfg rFinal).stk 13=RatInput.Encoder.packet (FirstRaw.firstValue input budget) (background 13) := by
      change rFinal.stk 13=_
      rw [rawFrame 13 (by decide)]
      exact nPrior
    have packet : (feeCfg rFinal).stk 12=feeOutput input (background 12) := by
      change rFinal.stk 15=_
      rw [rContents]
      change RatInput.Encoder.packet (input.experiment ⟨0,positive⟩).observationFee (nFinal.stk 12)=_
      rw [nFrames 12 (by decide)]
      simp only [feeOutput,dite_eq_left positive]
    have scratch : (feeCfg rFinal).stk 7=background 7 := by
      change rFinal.stk 7=_
      rw [rContents]
      change parsed.stk 7=_
      rw [rScratch]
      exact nScratch
    have cursor : ListBlank.mk ((feeCfg rFinal).stk 0)=ListBlank.mk (afterFee input contract budget++[true]) := by
      change ListBlank.mk (rFinal.stk 0)=_
      rw [rContents]
      change ListBlank.mk (parsed.stk 0)=_
      simpa only [Tape.mk₂,Tape.mk'_right₀] using congrArg Tape.right₀ rTape
    have contextEq : callerContext (feeCfg rFinal).var=context := by
      have held:=congrArg (fun memory : FirstRaw.RawContext C => memory.1.1) rContext
      exact held.trans nContext
    have frames : ∀ slot,¬Work slot→(feeCfg rFinal).stk slot=background slot := by
      intro slot untouched
      have safe : ¬FirstRaw.RawWork (feeRoles.symm slot) := by
        fin_cases slot
        all_goals first
          | exact of_decide_eq_true rfl
          | exact False.elim (untouched (by decide))
      change rFinal.stk (feeRoles.symm slot)=_
      rw [rawFrame _ safe]
      change nFinal.stk (feeRoles (feeRoles.symm slot))=_
      rw [Equiv.apply_symm_apply]
      exact nFrames slot (old_work slot untouched)
    have hasStage : (feeCfg rFinal).var.2.2=decide (I.stageCount≠0) := by
      have held:=congrArg (fun memory : FirstRaw.RawContext C => memory.2.2) rContext
      exact held.trans nFlag
    refine ⟨whole.trace,feeCfg rFinal,whole.first,whole.chain,whole.last,?_,natural,prior,packet,
      scratch,cursor,contextEq,frames,?_,hasStage⟩
    · change Option.map feeLabel rFinal.l=some .done
      rw [rActive]; rfl
    · simpa only [time,dite_eq_left positive] using whole.count
  · have zero : I.stageCount=0 := by omega
    let exit : State C:=⟨some .done,nFinal.var,nFinal.stk⟩
    have selected : TM2.step (program .halt) nFinal=some exit := by
      cases nFinal with
      | mk point memory contents =>
        change point=some .select at nActive
        subst point
        rw [select_step]
        change memory.2.2=decide (I.stageCount≠0) at nFlag
        rw [nFlag]
        simp [zero,exit]
    let finalSegment : Segment (.halt : Statement C) nFinal exit 2:=
      ⟨[nFinal,exit],rfl,List.isChain_cons_cons.mpr ⟨selected,List.isChain_singleton _⟩,rfl,Nat.le_refl _⟩
    let whole:=front.append finalSegment
    have wireEmpty : FirstRaw.wireSuffix input contract budget=[] := by
      unfold FirstRaw.wireSuffix FirstRaw.firstRemainder
      rw [dite_eq_right positive]; rfl
    have cursor : ListBlank.mk (exit.stk 0)=ListBlank.mk (afterFee input contract budget++[true]) := by
      have current:=congrArg Tape.right₀ nTape
      rw [wireEmpty] at current
      simpa only [exit,NatPrefix.tape,Tape.mk₂,Tape.mk'_right₀,afterFee,dite_eq_right positive,List.nil_append] using current
    refine ⟨whole.trace,exit,whole.first,whole.chain,whole.last,rfl,nNatural,nPrior,?_,nScratch,
      cursor,nContext,?_,?_,nFlag⟩
    · simpa only [feeOutput,dite_eq_right positive] using nFrames 12 (by decide)
    · intro slot untouched
      exact nFrames slot (old_work slot untouched)
    · simpa only [time,dite_eq_right positive,Nat.add_zero] using whole.count

end RootB234.PrepEntry.StageFront
