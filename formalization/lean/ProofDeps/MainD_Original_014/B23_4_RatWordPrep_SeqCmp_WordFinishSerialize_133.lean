module

public import B23_4_RatWordPrep_SeqCmp_WordFinishPaths_127
public import B23_4_RatWordPrep_SeqCmp_WordPublic_015

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

def wordCfg (before : SeqCmp.Word.State (FullStore.WordContext C)) : State C :=
  LabelMap.configuration wordLabel (StoreIso.configuration (FullStore.wordIso C) before)

theorem word_shared (before : State C) (r low high : Rat)
    (active : before.l=some (.word default)) (source : before.stk 15=SeqCmp.Word.input r low high [])
    (owned : ∀ slot,WordFold.Owned slot→before.stk slot=[]) :
    wordCfg (SeqCmp.Word.entry before.stk ((FullStore.wordIso C).symm before.var)
      r low high [] (before.stk 7))=before := by
  cases before with
  | mk point memory slots =>
    change point=some (.word default) at active
    subst point
    change (⟨some (.word default),FullStore.wordIso C ((FullStore.wordIso C).symm memory),
      RatPair.Link.initial slots (SeqCmp.Word.input r low high []) (slots 7)⟩ : State C)=_
    rw [Equiv.apply_symm_apply]
    congr 1
    funext slot
    fin_cases slot <;> first
    | rfl
    | exact source.symm
    | exact (owned _ (by decide)).symm

/-- Consumes the seven ACTUAL operands with the frozen three-comparator,
physical OR and whole WordOutput source. All registers are the original
allocated registers, observed through one static store isomorphism. -/
theorem actual_word (caller : Statement C) (before : State C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (active : before.l=some (.word default))
    (source : before.stk 15=SeqCmp.Word.input (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [])
    (owned : ∀ slot,WordFold.Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.finalize .clear) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk 13=wordOutput E target word ∧ final.stk 3=[] ∧
      final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) [] ∧ final.stk 7=before.stk 7 ∧
      run.trace.length≤SeqCmp.Word.coefficient*
        (SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree := by
  let memory := (FullStore.wordIso C).symm before.var
  obtain ⟨trace,final,facts⟩ := SeqCmp.Word.actual_polynomial before.stk memory
    (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7)
  have path := single_port_path (FullStore.wordIso C) wordLabel _ caller .done rfl
    trace _ final facts.first facts.chain facts.last facts.active
      (by intro point different; simp only [wordLabel,different,ite_false,program])
  let run : Segment caller before (wordCfg final) :=
    ⟨trace.map wordCfg,path.1.trans (congrArg some
      (word_shared before (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) active source owned)),path.2.1,path.2.2⟩
  refine ⟨wordCfg final,run,?_,?_,?_,?_,?_,?_,?_⟩
  · change final.l.map wordLabel=some (.finalize .clear)
    rw [facts.active]
    rfl
  · have base := congrArg (fun registers : FullStore.WordContext C × Bool × Bool => registers.1.2.2.2) facts.context_eq
    exact base
  · change final.stk 13=_
    rw [facts.contents]
    exact SeqCmp.Word.Public.original_data E target word
  · change final.stk 3=[]
    rw [facts.contents]
    rfl
  · change final.stk 15=_
    rw [facts.contents]
    rfl
  · change final.stk 7=_
    rw [facts.contents]
    rfl
  · simpa only [run,List.length_map] using facts.time

end B23_4_RatWordPrep.WordFinish
