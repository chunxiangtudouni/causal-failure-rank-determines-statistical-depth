module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038m

/-! Closed cached-to-plain loader: arbitrary actual first bit, real
read-clear into finite control, paid initialization, frozen042 copy, actual
SOURCE restore, record route, and actual DEST restore. No bit or width is
an executable argument, and all incoming old carry states are preserved. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033

def cachedPlainLocalCap (j : Nat) : Nat := 4+cachedPlainBodyCap j
theorem cached_plain_body_room (j : Nat) : cachedPlainBodyCap j≤cachedPlainLocalCap j := by
  unfold cachedPlainLocalCap
  omega
theorem cached_plain_reader_room (j : Nat) : 4≤cachedPlainLocalCap j := by
  unfold cachedPlainLocalCap
  omega

def cachedPlainBodies (j : Nat) (phase : Fin 2) : Machine (cachedPlainLocalCap j) :=
  padMachine (cached_plain_body_room j) (cachedPlainBodyMachine phase j)
def cachedPlainEnds (j : Nat) : Fin 2 → Fin (cachedPlainLocalCap j+1) :=
  fun _ => padLabel (cached_plain_body_room j) (cachedPlainBodyPort j)
def cachedPlainMachine (j : Nat) : Machine (totalStates 2 (cachedPlainLocalCap j)) :=
  observeThenMachine (cached_plain_reader_room j) (cachedPlainBodies j)
def cachedPlainFamily (p j : Nat) : Machine (totalStates p (totalStates 2 (cachedPlainLocalCap j))) :=
  observeFamily p (cached_plain_reader_room j) (cachedPlainBodies j)

theorem seen_observed_bit (bit : Bool) : seenBit (p:=0) (observedPhase bit)=bit := by
  cases bit <;> rfl

def cachedPlainTime (j : Nat) (records : List RecordSpec) (width gap : Nat) : Nat :=
  4*width^2+(2*cachedCost j records+2*gap+45)*width+
    2*cachedCost j records+3*gap+totalGap records+2*totalWidth records+9*j+43

theorem cached_plain_time_le (j : Nat) (records : List RecordSpec) (tail : List Bool) (gap : Nat) :
    2+cachedPlainBodyFee j records tail gap≤cachedPlainTime j records (false::tail).length gap := by
  have hf : ∀ r c, plainLoopFee (cachedCost j records) gap r c≤
      4*(r.length+c.length)+(2*cachedCost j records+2*gap+32) := by
    intro r c
    unfold plainLoopFee
    omega
  have hl := PA17TMRatArithmeticCopyLoop042.loopFee_affine
    (plainLoopFee (cachedCost j records) gap) 4 (2*cachedCost j records+2*gap+32) hf [] (false::tail)
  simp only [List.length_nil] at hl
  unfold cachedPlainBodyFee cachedDoneFee destinationFee cachedPlainTime
  nlinarith

theorem cached_plain_contract (p : Nat) (memory : Fin (p+1)) (j : Nat)
    (records : List RecordSpec) (hj : records.length=j) (archive tail : List Bool)
    (bit : Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedPlainFamily p j)
      (blockCfg memory
        (⟨0,Tape.mk₂ (false::archive) (cachedWord records (bit::tail) (plainWorkSuffix gap []))⟩ :
          MachineState (totalStates 2 (cachedPlainLocalCap j)))) trace
      (blockCfg memory
        (⟨observedPort (cachedPlainEnds j) bit,Tape.mk₂
          (destinationLeft .plain (cachedFinish records (false::archive) (bit::tail)) [] gap true)
          (PA17TMRatArithmeticCopy006.workspace (bit::tail))⟩ :
          MachineState (totalStates 2 (cachedPlainLocalCap j)))) ∧
      trace.length≤2+cachedPlainBodyFee j records tail gap ∧
      ∀ k, visitedSpace (cachedPlainFamily p j) inputLength (trace.take k) ≤
        inputLength+2*(2+cachedPlainBodyFee j records tail gap)+1 := by
  have hb := cached_plain_body_bounded (observedPhase bit) j records hj archive tail gap
  rw [seen_observed_bit] at hb
  have hp := PA17TMRatArithmeticFarLoad031.bounded_pad (cached_plain_body_room j) hb
  let suffix := true::(PSTRTMIncrement009.blocks tail++false::
    (cacheContext records++true::plainWorkSuffix gap []))
  have bodyRun : BoundedRun (cachedPlainBodies j (observedPhase bit))
      (Tape.mk₂ (false::archive) (false::suffix)) (cachedPlainEnds j (observedPhase bit))
      (Tape.mk₂ (destinationLeft .plain (cachedFinish records (false::archive) (bit::tail)) [] gap true)
        (PA17TMRatArithmeticCopy006.workspace (bit::tail))) (cachedPlainBodyFee j records tail gap) := by
    simpa only [cachedPlainBodies,cachedPlainEnds,cachedWord,flagged_cons,suffix,List.cons_append] using hp
  have h := observe_family_contract p memory (cached_plain_reader_room j) (cachedPlainBodies j)
    (cachedPlainEnds j) (false::archive) suffix bit _ (cachedPlainBodyFee j records tail gap) inputLength bodyRun
  simpa only [cachedPlainFamily,cachedWord,flagged_cons,suffix,List.cons_append] using h

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
