module

public import B23_4_RatWordPrep_SeqCmp_OriginalFeeClock_037

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace B23_4_RatWordPrep.OriginalFee.Public

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open Cost

theorem fixed_source (C : Type*) :
    ∃ (source : Label → Statement C) (clockA chargeA power : Nat),
      source .done=.halt ∧ 0<clockA ∧ 0<chargeA ∧ power=32 ∧
      ∀ (memory : RawGetter.Store C) (native : RatInput.Complement.CalleeFlags) (reader : RatInput.Complement.Reader)
        (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
        ∃ trace final beforeRead,Facts source memory native reader E target word trace final beforeRead ∧
          traceClockSum source trace≤clockA*((wordInput E target word).length+1)^power ∧
          chargedCost source trace≤chargeA*((wordInput E target word).length+1)^power := by
  refine ⟨program .halt,coefficient^2,chargedCoefficient,32,rfl,pow_pos coefficient_pos 2,chargedCoefficient_pos,rfl,?_⟩
  intro memory native reader E target word
  obtain ⟨trace,final,beforeRead,facts⟩ := actual_polynomial memory native reader E target word
  exact ⟨trace,final,beforeRead,facts,traceClockSum_le facts,chargedCost_le facts⟩

end B23_4_RatWordPrep.OriginalFee.Public
