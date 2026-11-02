module

public import B23_4_WordTM0_Original001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_WordTM0.Public

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

/-- A single finite Bool machine and fixed positive constants before all
original WORD inputs. Runs includes literal TM0.init and actual eval
membership; both time and every visited-space prefix use this same run. -/
theorem original_actual :
    ∃ states : Nat,∃ code : Machine states,∃ port : Fin (states+1),∃ coefficient degree : Nat,
      0<coefficient ∧ 0<degree ∧
      ∀ (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord),
        ∃ trace final,Runs code (wordInput E target word) trace final ∧ final.q=port ∧
          TM0.step code final=none ∧ final.Tape.right₀=ListBlank.mk (wordOutput E target word) ∧
          trace.length≤coefficient*((wordInput E target word).length+word.1+1)^degree ∧
          ∀ clock,visitedSpace code (wordInput E target word).length (trace.take clock)≤
            coefficient*((wordInput E target word).length+word.1+1)^degree := by
  simpa only [scale] using actual_uniform

/-- Exact unchanged word component of RCC.localArithmeticClaims. -/
theorem original_computes :
    ∃ states : Nat,∃ code : Machine states,∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧
      ∀ (E : BinaryExperiment) (target : Rat),0<target→target≤1/4→∀ word : E.StoppedWord,
        computes code (wordInput E target word) (wordOutput E target word)
          (coefficient*((wordInput E target word).length+word.1+1)^degree)
          (coefficient*((wordInput E target word).length+word.1+1)^degree) := computes_uniform

end B23_4_WordTM0.Public
