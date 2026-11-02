module

public import B23_4_RatWordPrep_SeqCmp_WordScale_014

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.SeqCmp.Word.Public

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation

theorem original_data (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) :
    encode [.rational (E.rationalWordOdds word),
      boolDatum (decide (E.rationalWordOdds word≤p/(1-p)) || decide ((1-p)/p≤E.rationalWordOdds word)),
      boolDatum (decide ((1:Rat)≤E.rationalWordOdds word))]=wordOutput E p word := by
  by_cases lower : E.rationalWordOdds word≤p/(1-p)
  all_goals by_cases upper : (1-p)/p≤E.rationalWordOdds word
  all_goals simp [wordOutput,BinaryExperiment.rationalWordHits,BinaryExperiment.rationalWordMAP,lower,upper]

/-- Exact original WordOutput, from explicitly staged operand packets.
This does not claim production of those packets from wordInput. -/
theorem fixed_source (C : Type*) :
    ∃ source : Label → Statement C, source .done=.halt ∧
      ∀ (background : RatInput.Stack → List Bool) (memory : Store C)
        (E : BinaryExperiment) (p : Rat) (word : E.StoppedWord) (tail scratch : List Bool),
        ∃ trace final,
          Facts source background memory (E.rationalWordOdds word) (p/(1-p)) ((1-p)/p) tail scratch trace final ∧
          final.stk 13=wordOutput E p word ∧
          final.stk 15=RatInput.Encoder.packet (E.rationalWordOdds word) tail ∧ final.stk 7=scratch ∧
          final.stk 3=[] ∧ final.stk 4=[] ∧ final.stk 5=[] ∧ final.stk 6=[] ∧
          final.stk 8=[] ∧ final.stk 9=[] ∧ final.stk 12=[] ∧ final.stk 14=[] := by
  refine ⟨program .halt,rfl,?_⟩
  intro background memory E p word tail scratch
  obtain ⟨trace,final,facts⟩ := actual_polynomial background memory (E.rationalWordOdds word) (p/(1-p)) ((1-p)/p) tail scratch
  refine ⟨trace,final,facts,?_,?_⟩
  · rw [facts.contents]
    exact original_data E p word
  · rw [facts.contents]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

example : 0<coefficient := coefficient_pos
example : degree=4 := degree_eq_four

end B23_4_RatWordPrep.SeqCmp.Word.Public
