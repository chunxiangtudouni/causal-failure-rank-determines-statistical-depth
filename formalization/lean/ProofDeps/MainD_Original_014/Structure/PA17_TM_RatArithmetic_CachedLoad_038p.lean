module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038o
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038r

/-! Closed cached-to-shared-B loader. The actual source head bit selects
the precompiled observation row, both SOURCE and B LSBs are physically
restored, and A/prior records/all incoming carry bits are preserved. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033

def cachedSharedLocalCap (j : Nat) : Nat := 4+cachedSharedBodyCap j
theorem cached_shared_body_room (j : Nat) : cachedSharedBodyCap j≤cachedSharedLocalCap j := by
  unfold cachedSharedLocalCap
  omega
theorem cached_shared_reader_room (j : Nat) : 4≤cachedSharedLocalCap j := by
  unfold cachedSharedLocalCap
  omega
def cachedSharedBodies (j : Nat) (phase : Fin 2) : Machine (cachedSharedLocalCap j) :=
  padMachine (cached_shared_body_room j) (cachedSharedBodyMachine phase j)
def cachedSharedEnds (j : Nat) : Fin 2 → Fin (cachedSharedLocalCap j+1) :=
  fun _ => padLabel (cached_shared_body_room j) (cachedSharedBodyPort j)
def cachedSharedFamily (p j : Nat) : Machine (totalStates p (totalStates 2 (cachedSharedLocalCap j))) :=
  observeFamily p (cached_shared_reader_room j) (cachedSharedBodies j)

def cachedSharedTime (j : Nat) (records : List RecordSpec) (width aWidth gap : Nat) : Nat :=
  4*width^2+(2*cachedCost j records+2*gap+4*aWidth+55)*width+
    2*cachedCost j records+3*gap+6*aWidth+totalGap records+2*totalWidth records+9*j+56

theorem cached_shared_time_le (j : Nat) (records : List RecordSpec) (tail a : List Bool) (gap : Nat) :
    2+cachedSharedBodyFee j records tail a gap≤cachedSharedTime j records (false::tail).length a.length gap := by
  have hl := PA17TMRatArithmeticMul047.shared_loop_fee_le (cachedCost j records) gap a [] (false::tail)
  simp only [List.length_nil] at hl
  unfold cachedSharedBodyFee cachedDoneFee destinationFee cachedSharedTime
  nlinarith

theorem cached_shared_contract (p : Nat) (memory : Fin (p+1)) (j : Nat)
    (records : List RecordSpec) (hj : records.length=j) (archive tail a : List Bool)
    (bit : Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedSharedFamily p j)
      (blockCfg memory
        (⟨0,Tape.mk₂ (false::archive) (cachedWord records (bit::tail)
          (PA17TMRatArithmeticPairExcursion041.workSuffix gap a []))⟩ :
          MachineState (totalStates 2 (cachedSharedLocalCap j)))) trace
      (blockCfg memory
        (⟨observedPort (cachedSharedEnds j) bit,Tape.mk₂
          (destinationLeft .shared (cachedFinish records (false::archive) (bit::tail)) a gap true)
          (PA17TMRatArithmeticCopy006.workspace (bit::tail))⟩ :
          MachineState (totalStates 2 (cachedSharedLocalCap j)))) ∧
      trace.length≤2+cachedSharedBodyFee j records tail a gap ∧
      ∀ k, visitedSpace (cachedSharedFamily p j) inputLength (trace.take k) ≤
        inputLength+2*(2+cachedSharedBodyFee j records tail a gap)+1 := by
  have hb := cached_shared_body_bounded (observedPhase bit) j records hj archive tail a gap
  rw [seen_observed_bit] at hb
  have hp := PA17TMRatArithmeticFarLoad031.bounded_pad (cached_shared_body_room j) hb
  let suffix := true::(PSTRTMIncrement009.blocks tail++false::
    (cacheContext records++true::PA17TMRatArithmeticPairExcursion041.workSuffix gap a []))
  have bodyRun : BoundedRun (cachedSharedBodies j (observedPhase bit))
      (Tape.mk₂ (false::archive) (false::suffix)) (cachedSharedEnds j (observedPhase bit))
      (Tape.mk₂ (destinationLeft .shared (cachedFinish records (false::archive) (bit::tail)) a gap true)
        (PA17TMRatArithmeticCopy006.workspace (bit::tail))) (cachedSharedBodyFee j records tail a gap) := by
    simpa only [cachedSharedBodies,cachedSharedEnds,cachedWord,flagged_cons,suffix,List.cons_append] using hp
  have h := observe_family_contract p memory (cached_shared_reader_room j) (cachedSharedBodies j)
    (cachedSharedEnds j) (false::archive) suffix bit _ (cachedSharedBodyFee j records tail a gap) inputLength bodyRun
  simpa only [cachedSharedFamily,cachedWord,flagged_cons,suffix,List.cons_append] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
