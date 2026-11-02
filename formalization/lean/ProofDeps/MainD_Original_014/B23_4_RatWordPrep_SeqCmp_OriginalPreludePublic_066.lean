module

public import B23_4_RatWordPrep_SeqCmp_OriginalPreludeClock_065

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalPrelude.Public

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open Cost

theorem fixed_source (C : Type*) :
    ∃ (source : Label → Statement C) (clockA chargeA power : Nat),
      source .done=.halt ∧ TM2.Supports source (Finset.univ : Finset Label) ∧
      0<clockA ∧ 0<chargeA ∧ power=32 ∧
      ∀ (context : C) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
        ∃ trace final beforeRead,Facts source context E target word trace final beforeRead ∧
          traceClockSum source trace ≤ clockA*((wordInput E target word).length+1)^power ∧
          chargedCost source trace ≤ chargeA*((wordInput E target word).length+1)^power := by
  refine ⟨program .halt,coefficient^2,chargedCoefficient,32,rfl,supports,
    pow_pos coefficient_pos 2,chargedCoefficient_pos,rfl,?_⟩
  intro context E target word
  obtain ⟨trace,final,beforeRead,facts⟩:=actual_polynomial context E target word
  exact ⟨trace,final,beforeRead,facts,traceClockSum_le facts,chargedCost_le facts⟩

/-- Literal original input and default finite auxiliary store. This returns
alphabet8 and fee/prior packets15, not the final native WordOutput endpoint. -/
theorem from_default (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    ∃ trace final beforeRead,Facts (program (C := Unit) .halt) () E target word trace final beforeRead ∧
      trace.head?=some (TM2.init (Γ := RatInput.Alphabet) (Λ := Label) (σ := Store Unit) 0 (wordInput E target word)) := by
  obtain ⟨trace,final,beforeRead,facts⟩:=actual_polynomial () E target word
  exact ⟨trace,final,beforeRead,facts,facts.first.trans (congrArg some (initial_default _))⟩

end B23_4_RatWordPrep.OriginalPrelude.Public
