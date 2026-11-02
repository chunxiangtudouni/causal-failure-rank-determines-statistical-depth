module
public import RootPaper_Reference_ScalarBounds018
public import RootPaper_Reference_Whole016
public import RootPaper_TableCost_Input011

/-! WORD operands come from the actual measured snapshot and kernel.
The shared input-size theorem is consumed directly; no wire producer,
extra width input, or separate WORD answer is introduced. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace RootPaper.Reference.Charged
open PaperProofs.Common PaperProofs.Statistics PaperProofs.Common.Native
open RootPaper.Reference RationalControllerComputation PSTRWordBool
variable {I : Instance}

theorem kernel_target_width (available : Finset I.Tool) (budget : Rat) (cache : ReferenceReplayCache I)
    (B : Nat) (valid : 0<budget ∧ budget≤1/2) (width : RatInput.Encoder.fieldSize budget≤B)
    (events : cache.events.length≤B) (stages : I.stageCount≤B) (target : Rat)
    (selected : (kernel I available budget cache).target=some target) :
    RatInput.Encoder.fieldSize target≤6144*(B+1) := by
  have actual : referenceAvailableCacheTarget I available budget cache=some target :=
    (kernel_values available budget cache).2.2.symm.trans selected
  cases blocked : cache.halted || decide (cache.phase≠.testing) with
  | true => simp only [referenceAvailableCacheTarget,blocked,ite_true] at actual;cases actual
  | false =>
      simp only [referenceAvailableCacheTarget,blocked,Bool.false_eq_true,ite_false] at actual
      obtain ⟨kind,kindEq,rest⟩:=Option.bind_eq_some_iff.mp actual
      obtain ⟨risk,current,rest⟩:=Option.bind_eq_some_iff.mp rest
      by_cases live : 0<risk ∧ risk≤1/4 ∧ cache.events.length≤I.stageCount
      · rw [ite_eq_left live] at rest
        have path : (referenceBudgetPath (budget/2) cache.events).bind (referenceBudgetTarget kind)=some target := by
          change referenceBudgetPath (budget/2) cache.events=some risk at current
          rw [current,Option.bind_some]
          exact rest
        have kindSource : (kernel I available budget cache).classification=some kind :=
          (kernel_values available budget cache).1.trans kindEq
        have depth:=kernel_kind_depth available budget cache kind kindSource
        have bounded:=RootB236.RiskFold.original_target_width budget cache.events kind target valid path
        have whole:=Nat.add_le_add_right (Nat.add_le_add
          (Nat.add_le_add (Nat.mul_le_mul_left 4 width) (Nat.mul_le_mul_left 12 events))
          (Nat.mul_le_mul_left 3 (depth.trans (Nat.add_le_add_right stages 1)))) 23
        have paid:=bounded.trans (Nat.mul_le_mul_left 128 whole)
        omega
      · rw [ite_eq_right live] at rest
        cases rest

theorem wordCalculation_length (E : BinaryExperiment) (items : List Nat)
    (valid : ∀ symbol∈items,symbol<E.alphabetSize) : (wordCalculation E items valid).1.1=items.length :=
  (count_spec items).1

theorem testingCalculation_word_origin (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (stage : I.Stage) (observations : List Nat) (data : Kernel I) (call : WordCall input)
    (member : call∈(testingCalculation input quota stage observations data).words) :
    data.target=some call.target ∧ call.word.1=observations.length := by
  unfold testingCalculation at member
  cases classified : data.classification with
  | none => simp only [classified] at member;cases member
  | some kind =>
      simp only [classified] at member
      cases kind with
      | infiniteRank => cases member
      | noTool | finiteBad depth =>
          cases selected : data.target with
          | none => simp only [selected] at member;cases member
          | some target =>
              simp only [selected] at member
              by_cases valid : (validate (fun symbol => decide (symbol<(input.experiment stage).alphabetSize)) observations).1=true
              · rw [dite_eq_left valid] at member
                have same:=List.mem_singleton.mp member
                subst call
                refine ⟨rfl,?_⟩
                exact (count_spec observations).1
              · rw [dite_eq_right valid] at member
                cases member

theorem decisionCalculation_word_origin (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (cache : ReferenceReplayCache I) (view : Snapshot I) (data : Kernel I) (call : WordCall input)
    (member : call∈(decisionCalculation input quota cache view data).words) :
    data.target=some call.target ∧ call.word.1≤view.observations.length := by
  unfold decisionCalculation at member
  cases halted : cache.halted with
  | true => simp only [halted,ite_true] at member;cases member
  | false =>
      simp only [halted,Bool.false_eq_true,ite_false] at member
      cases current : view.stage with
      | none => simp only [current] at member;cases member
      | some stage =>
          simp only [current] at member
          cases phase : cache.phase with
          | testing =>
              simp only [phase] at member
              have source:=testingCalculation_word_origin input quota stage view.observations data call member
              exact ⟨source.1,source.2.le⟩
          | written | reported | allocated tool | executed tool =>
              simp only [phase] at member
              cases member

def ScalarMarker : ScalarCall I→Prop
  | .word _ _ _ => True
  | _ => False

theorem testingCalculation_markers (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (stage : I.Stage) (observations : List Nat) (data : Kernel I) (call : ScalarCall I)
    (member : call∈(testingCalculation input quota stage observations data).scalar) : ScalarMarker call := by
  unfold testingCalculation at member
  cases classified : data.classification with
  | none => simp only [classified] at member;cases member
  | some kind =>
      simp only [classified] at member
      cases kind with
      | infiniteRank => cases member
      | noTool | finiteBad depth =>
          cases selected : data.target with
          | none => simp only [selected] at member;cases member
          | some target =>
              simp only [selected] at member
              by_cases valid : (validate (fun symbol => decide (symbol<(input.experiment stage).alphabetSize)) observations).1=true
              · rw [dite_eq_left valid] at member
                cases List.mem_singleton.mp member
                trivial
              · rw [dite_eq_right valid] at member
                cases member

theorem decisionCalculation_markers (input : StatisticalInput I) (quota : I.Stage→Nat×Nat)
    (cache : ReferenceReplayCache I) (view : Snapshot I) (data : Kernel I) (call : ScalarCall I)
    (member : call∈(decisionCalculation input quota cache view data).scalar) : ScalarMarker call := by
  unfold decisionCalculation at member
  cases halted : cache.halted with
  | true => simp only [halted,ite_true] at member;cases member
  | false =>
      simp only [halted,Bool.false_eq_true,ite_false] at member
      cases current : view.stage with
      | none => simp only [current] at member;cases member
      | some stage =>
          simp only [current] at member
          cases phase : cache.phase with
          | testing =>
              simp only [phase] at member
              exact testingCalculation_markers input quota stage view.observations data call member
          | written | reported | allocated tool | executed tool =>
              simp only [phase] at member
              cases member

theorem controllerCalculation_callBound (input : StatisticalInput I) (available : Finset I.Tool) (budget : Rat)
    (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) (valid : 0<budget ∧ budget≤1/2)
    (call : ScalarCall I) (member : call∈(controllerCalculation input available budget quota history).scalar) :
    ScalarMarker call ∨ RootPaper.TableCost.CallBound
      (2*RatInput.Encoder.fieldSize budget+6*history.length+4) (I.stageCount+1) call := by
  dsimp only [controllerCalculation] at member
  cases parsed : (parseCalculation input available budget history).value with
  | none =>
      rw [parsed] at member
      exact Or.inr (parseCalculation_callBound input available budget history valid call member)
  | some pair =>
      rcases pair with ⟨cache,view⟩
      rw [parsed] at member
      dsimp only at member
      have actual:=kernelCalculation_value available budget cache view
        (parseCalculation_view input available budget history cache view parsed)
      rw [actual] at member
      simp only [List.mem_append] at member
      rcases member with (earlier|current)|last
      · exact Or.inr (parseCalculation_callBound input available budget history valid call earlier)
      · have bounded:=(parseCalculation_bounds input available budget history).result cache view parsed
        have depths:=parseCalculation_depths input available budget history cache view parsed
        exact Or.inr (callBound_mono (by have reports:=bounded.2.2;omega) (Nat.le_refl _)
          call (kernel_callBound available budget cache valid depths call current))
      · exact Or.inl (decisionCalculation_markers input quota cache view (kernel I available budget cache) call last)

theorem controllerCalculation_words (input : StatisticalInput I) (C : Contract I) (available : Finset I.Tool)
    (budget : Rat) (quota : I.Stage→Nat×Nat) (history : List (VisibleEvent I)) (B : Nat)
    (valid : 0<budget ∧ budget≤1/2) (original : arithmeticScale input C budget≤B) (room : history.length≤B)
    (call : WordCall input) (member : call∈(controllerCalculation input available budget quota history).words) :
    (wordInput (input.experiment call.stage) call.target call.word).length+call.word.1+1≤100000*(B+1)^2 := by
  dsimp only [controllerCalculation] at member
  cases parsed : (parseCalculation input available budget history).value with
  | none => rw [parsed] at member;cases member
  | some pair =>
      rcases pair with ⟨cache,view⟩
      rw [parsed] at member
      dsimp only at member
      have correct:=parseCalculation_view input available budget history cache view parsed
      have actual:=kernelCalculation_value available budget cache view correct
      rw [actual] at member
      have source:=decisionCalculation_word_origin input quota cache view (kernel I available budget cache) call member
      have bounded:=(parseCalculation_bounds input available budget history).result cache view parsed
      have stages : I.stageCount≤B := by unfold arithmeticScale inputSize at original;omega
      have width : RatInput.Encoder.fieldSize budget≤B :=
        (RootPaper.Prep.input_rat_field I input C budget budget (by
          simp only [RootPaper.Prep.originalData,List.mem_append,List.mem_singleton];tauto)).trans original
      have target:=kernel_target_width available budget cache B valid width (bounded.2.2.trans room) stages call.target source.1
      have observed : view.observations.length≤cache.seen.length := by rw [correct];exact snapshot_observations_length cache
      have material:=(RootPaper.Prep.experiment_material_le_input I input C budget call.stage).trans
        ((RootPaper.Prep.original_bits_le_scale I input C budget).trans original)
      have alphabet:=((RootB23.PrepScalar.each_alphabet_le_total I input call.stage).trans
        (RootB23.PrepScalar.alphabet_total_le_scale I input C budget)).trans original
      exact RootPaper.TableCost.word_input_size _ _ _ B material target alphabet
        (source.2.trans (observed.trans (bounded.1.trans room)))

end RootPaper.Reference.Charged
