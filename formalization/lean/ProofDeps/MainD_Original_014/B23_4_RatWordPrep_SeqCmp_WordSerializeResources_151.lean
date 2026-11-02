module

public import B23_4_RatWordPrep_SeqCmp_WordResourceJoin_142
public import B23_4_RatWordPrep_SeqCmp_WordFinishSerialize_133

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

variable {C : Type*}

theorem actual_word_resources (caller : Statement C) (before : State C)
    (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (active : before.l=some (.word default))
    (source : before.stk 15=SeqCmp.Word.input (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [])
    (owned : ∀ slot,WordFold.Owned slot→before.stk slot=[]) :
    ∃ (final : State C) (run : Segment caller before final),
      final.l=some (.finalize .clear) ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk=RatInput.Encoder.bank (RatPair.Link.clean before.stk)
        (RatInput.Encoder.packet (E.rationalWordOdds word) []) (before.stk 7)
        [] [] [] [] (wordOutput E target word) [] [] ∧
      RunBounds caller run
        (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree)
        (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree)
        (SeqCmp.Word.coefficient*(SeqCmp.Word.inputScale before.stk (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7))^SeqCmp.Word.degree) := by
  let iso := FullStore.wordIso C
  let memory := iso.symm before.var
  let old := SeqCmp.Word.program (C := FullStore.WordContext C) .halt
  obtain ⟨trace,final,facts⟩ := SeqCmp.Word.actual_polynomial before.stk memory
    (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) [] (before.stk 7)
  have same (point : SeqCmp.Word.Label) (different : point≠.done) :
      program caller (wordLabel point)=LabelMap.statement wordLabel (StoreIso.statement iso (old point)) := by
    simp only [wordLabel,different,ite_false,program]
    rfl
  have path := single_port_path iso wordLabel old caller .done rfl trace _ final
    facts.first facts.chain facts.last facts.active same
  let run : Segment caller before (mappedCfg iso wordLabel final) :=
    ⟨trace.map (mappedCfg iso wordLabel),path.1.trans (congrArg some
      (word_shared before (E.rationalWordOdds word) (target/(1-target)) ((1-target)/target) active source owned)),path.2.1,path.2.2⟩
  refine ⟨mappedCfg iso wordLabel final,run,?_,?_,?_,?_⟩
  · change final.l.map wordLabel=some (.finalize .clear)
    rw [facts.active]
    rfl
  · exact congrArg (fun registers : FullStore.WordContext C × Bool × Bool => registers.1.2.2.2) facts.context_eq
  · change final.stk=_
    rw [facts.contents,SeqCmp.Word.Public.original_data]
  · constructor
    · simpa only [run,List.length_map] using facts.time
    · intro current member slot
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      exact (facts.boundaries original present).1 slot
    · intro current member point selected node inside slot
      change current∈(trace.map (mappedCfg iso wordLabel)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change original.l.map wordLabel=some point at selected
      obtain ⟨oldPoint,oldActive,renamed⟩ := Option.map_eq_some_iff.mp selected
      have different : oldPoint≠.done := by intro equal; subst oldPoint; exact (facts.proper original present).1 oldActive
      have body := same oldPoint different
      rw [←renamed] at inside
      change node∈AuxWorkspace.nodes (program caller (wordLabel oldPoint)) (iso original.var) original.stk at inside
      rw [mapped_nodes iso wordLabel old caller oldPoint original.var original.stk body] at inside
      obtain ⟨oldNode,oldInside,rfl⟩ := List.mem_map.mp inside
      exact (((facts.proper original present).2 oldPoint oldActive).1 oldNode oldInside).1 slot
    · intro current member point selected
      change current∈(trace.map (mappedCfg iso wordLabel)).dropLast at member
      rw [←List.map_dropLast] at member
      obtain ⟨original,present,rfl⟩ := List.mem_map.mp member
      change original.l.map wordLabel=some point at selected
      obtain ⟨oldPoint,oldActive,renamed⟩ := Option.map_eq_some_iff.mp selected
      have different : oldPoint≠.done := by intro equal; subst oldPoint; exact (facts.proper original present).1 oldActive
      have body := same oldPoint different
      rw [←renamed]
      change ScannerStatement.clock (program caller (wordLabel oldPoint)) (iso original.var) original.stk≤_
      rw [body,clock_labelMap,clock_storeIso]
      exact ((facts.proper original present).2 oldPoint oldActive).2

end B23_4_RatWordPrep.WordFinish.Resources
