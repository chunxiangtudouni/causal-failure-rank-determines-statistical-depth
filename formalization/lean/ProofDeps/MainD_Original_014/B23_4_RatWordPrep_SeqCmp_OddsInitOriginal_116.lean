module

public import B23_4_RatWordPrep_SeqCmp_OddsInitSwap_114
public import B23_4_RatWordPrep_SeqCmp_OddsInitDivide_115

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.OddsInit

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

instance swapFrameDecidable (slot : RatInput.Stack) : Decidable (SwapFrame slot) := by unfold SwapFrame; infer_instance

theorem actual_initialize (caller : Statement C) (before : State C) (fee prior comp : Rat)
    (active : before.l=some (.fee 0)) (owned : ∀ slot,Owned slot→before.stk slot=[])
    (source : before.stk 15=RatInput.Encoder.packet fee
      (RatInput.Encoder.packet comp (RatInput.Encoder.packet prior []))) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some .done ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk 15=RatInput.Encoder.packet (prior/comp) [] ∧ final.stk 7=before.stk 7 ∧
      (∀ slot,Owned slot→final.stk slot=[]) ∧
      ∀ slot,¬RatPair.Link.Work slot→final.stk slot=before.stk slot := by
  obtain ⟨middle,swapRun,port,context,packet,empty4,empty13,empty14,frame,_time⟩ := actual_swap caller before
    fee prior comp active (owned 4 (by decide)) (owned 13 (by decide)) (owned 14 (by decide)) source
  have middleOwned : ∀ slot,Owned slot→middle.stk slot=[] := by
    intro slot selected
    fin_cases slot <;> first
    | exact empty4
    | exact empty13
    | exact empty14
    | exact (frame _ (by decide)).trans (owned _ (by decide))
    | simp [Owned] at selected
  obtain ⟨final,divRun,finalPort,divContext,output,scratch,finalOwned,finalFrame,_divTime⟩ :=
    actual_divide caller middle prior comp [] port packet middleOwned
  let whole := swapRun.append divRun
  refine ⟨final,whole,finalPort,?_,output,?_,finalOwned,?_⟩
  · exact (congrArg (fun memory : WordPack.Store C => memory.2.2) divContext).trans context
  · exact scratch.trans (frame 7 (by decide))
  · intro slot untouched
    have n4 : slot≠4 := by intro equal; subst slot; exact untouched (by decide)
    have n13 : slot≠13 := by intro equal; subst slot; exact untouched (by decide)
    have n14 : slot≠14 := by intro equal; subst slot; exact untouched (by decide)
    have n15 : slot≠15 := by intro equal; subst slot; exact untouched (by decide)
    exact (finalFrame slot untouched).trans (frame slot ⟨n4,n13,n14,n15⟩)

/-- Entire original input to initial rational prior odds plus the original
lookup data. Fee disposal, the packet exchange and division are all paid
on the same fixed source with all future finite auxiliaries preallocated. -/
theorem actual_original (caller : Statement C) (context : C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ (final : State C) (_run : Segment caller (entry context (wordInput E target word)) final),
      final.l=some .done ∧
      OriginalFee.context (OriginalPrelude.feeMemory final.var.2.2.2)=context ∧
      final.stk 0=PacketLists.naturals (WordFields.symbolValues E word) [] ∧
      final.stk 1=NatField.packet E.alphabetSize (RatInput.Encoder.packet target []) ∧
      final.stk 2=PacketLists.rats (Channels.channelValues E) [] ∧
      final.stk 15=RatInput.Encoder.packet (E.priorOne/(1-E.priorOne)) [] ∧ final.stk 7=[] ∧
      (∀ slot,Owned slot→final.stk slot=[]) := by
  obtain ⟨packed,packRun,_digits,active,contextEq,wordQueue,metadata,table,source,
    _counter,_zero,_width,_left,owned⟩ := WordPack.actual_original .halt context E target word
  have path := prep_path caller default packRun.trace _ packed packRun.first packRun.chain packRun.last active
  let beforeInit := prepCfg default packed
  let front : Segment caller (entry context (wordInput E target word)) beforeInit :=
    ⟨packRun.trace.map (prepCfg default),path.1,path.2.1,path.2.2⟩
  have atInit : beforeInit.l=some (.fee 0) := by
    change packed.l.map prepLabel=_
    rw [active]
    rfl
  have clean : ∀ slot,Owned slot→beforeInit.stk slot=[] := by
    intro slot selected
    fin_cases slot <;> first
    | exact owned.1
    | exact owned.2.1
    | exact owned.2.2.1
    | exact owned.2.2.2.1
    | exact owned.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.2.2.1
    | exact owned.2.2.2.2.2.2.2.2.2
    | simp [Owned] at selected
  obtain ⟨final,initRun,atDone,baseEq,odds,scratch,finalOwned,frame⟩ := actual_initialize caller beforeInit
    E.observationFee E.priorOne (1-E.priorOne) atInit clean source
  let whole := front.append initRun
  refine ⟨final,whole,atDone,?_,?_,?_,?_,odds,?_,finalOwned⟩
  · exact (congrArg (fun memory => OriginalFee.context (OriginalPrelude.feeMemory memory)) baseEq).trans contextEq
  · exact (frame 0 (by decide)).trans wordQueue
  · exact (frame 1 (by decide)).trans metadata
  · exact (frame 2 (by decide)).trans table
  · exact scratch.trans owned.2.2.2.2.1

end B23_4_RatWordPrep.OddsInit
