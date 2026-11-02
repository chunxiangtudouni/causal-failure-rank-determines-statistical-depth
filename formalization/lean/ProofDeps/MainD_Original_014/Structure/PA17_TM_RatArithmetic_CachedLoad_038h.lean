module
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038g
public import Structure.PA17_TM_RatArithmetic_CachedLoad_038f
public import Structure.PA17_TM_RatArithmetic_PairDestination_040b

/-! One static destination transport table. Plain data follows the anchor
guard; shared operand B follows A's actual END. Padding keeps the real
plain HALT4, whereas the shared program really halts at6. No width, bit,
record metadata, or input value selects the executable code. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)
open PA17TMRatArithmeticBankWalk033

inductive Destination where
  | plain
  | shared
  deriving DecidableEq

def destinationMachine : Destination → Machine 6
  | .plain => padMachine (by decide : 4≤6) PA17TMRatArithmeticFarLoad031.toDestMachine
  | .shared => PA17TMRatArithmeticPairDestination040.outToBMachine

def destinationPort : Destination → Fin 7
  | .plain => padLabel (by decide : 4≤6) 4
  | .shared => 6

def destinationWord : Destination → List Bool → List Bool → List Bool
  | .plain, _, tail => false::tail
  | .shared, a, tail => PSTRTMIncrement009.blocks a++false::false::tail

def destinationSuffix (kind : Destination) (a tail : List Bool) (gap : Nat) : List Bool :=
  List.replicate gap false++true::false::destinationWord kind a tail

def destinationLeft : Destination → List Bool → List Bool → Nat → Bool → List Bool
  | .plain, archive, _, gap, oldBit => false::true::(List.replicate gap false++oldBit::archive)
  | .shared, archive, a, gap, oldBit => false::(PSTRTMRawNat010.leftBlocks a.reverse++false::true::
      (List.replicate gap false++oldBit::archive))

def destinationFee : Destination → Nat → Nat → Nat
  | .plain, _, gap => gap+5
  | .shared, width, gap => gap+2*width+7

theorem destination_bounded (kind : Destination) (oldBit : Bool) (archive a tail : List Bool) (gap : Nat) :
    BoundedRun (destinationMachine kind)
      (Tape.mk₂ archive (oldBit::destinationSuffix kind a tail gap)) (destinationPort kind)
      (Tape.mk₂ (destinationLeft kind archive a gap oldBit) (false::tail))
      (destinationFee kind a.length gap) := by
  cases kind with
  | plain =>
    exact PA17TMRatArithmeticFarLoad031.bounded_pad (by decide : 4≤6)
      (PA17TMRatArithmeticFarLoad031.toDest_bounded gap archive oldBit (false::tail))
  | shared => exact PA17TMRatArithmeticPairDestination040.out_to_B_bounded oldBit archive a tail gap

def originalToDestCap (j : Nat) : Nat := originalEOFCap j+6+1

def originalToDestMachine (route : PA17TMRatArithmeticFarLoad031.FarRoute) (j : Nat)
    (kind : Destination) : Machine (originalToDestCap j) :=
  PSTRTMSeq005.seqMachine (a:=originalEOFCap j) (b:=6)
    (originalEOFMachine route j) (destinationMachine kind)

def originalToDestPort (j : Nat) (kind : Destination) : Fin (originalToDestCap j+1) :=
  PSTRTMSeq005.rightLabel (a:=originalEOFCap j) (destinationPort kind)

/-- Original footer remains physically FALSE, including after crossing a
nonempty bank. No per-bit temporary TRUE finish is used at EOF. -/
theorem original_to_dest_bounded (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (records : List RecordSpec) (hj : records.length=j) (kind : Destination)
    (left a tail : List Bool) (gap : Nat) :
    BoundedRun (originalToDestMachine route j kind)
      (Tape.mk₂ (false::left) (context++false::bankTail records (destinationSuffix kind a tail gap)))
      (originalToDestPort j kind)
      (Tape.mk₂ (destinationLeft kind (bankLeftAny false (finish left []) records) a gap
        (bankEndBitAny false records)) (false::tail))
      (cost+totalGap records+2*totalWidth records+9*j+3+destinationFee kind a.length gap) := by
  have he := original_EOF_bounded route context finish cost correct j records hj left
    (destinationSuffix kind a tail gap)
  have hd := destination_bounded kind (bankEndBitAny false records)
    (bankLeftAny false (finish left []) records) a tail gap
  simpa only [originalToDestMachine,originalToDestCap,originalToDestPort,bankEndAny] using he.seq hd

theorem original_to_dest_contract (route : PA17TMRatArithmeticFarLoad031.FarRoute)
    (context : List Bool) (finish : List Bool → List Bool → List Bool) (cost : Nat)
    (correct : PA17TMRatArithmeticFarLoad031.RouteCorrect route context finish cost)
    (j : Nat) (records : List RecordSpec) (hj : records.length=j) (kind : Destination)
    (left a tail : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalToDestMachine route j kind)
      ⟨0,Tape.mk₂ (false::left) (context++false::bankTail records (destinationSuffix kind a tail gap))⟩ trace
      ⟨originalToDestPort j kind,Tape.mk₂
        (destinationLeft kind (bankLeftAny false (finish left []) records) a gap
          (bankEndBitAny false records)) (false::tail)⟩ ∧
      trace.length≤cost+totalGap records+2*totalWidth records+9*j+3+destinationFee kind a.length gap ∧
      ∀ k, visitedSpace (originalToDestMachine route j kind) inputLength (trace.take k) ≤
        inputLength+2*(cost+totalGap records+2*totalWidth records+9*j+3+destinationFee kind a.length gap)+1 := by
  obtain ⟨trace,hr,hl⟩ := original_to_dest_bounded route context finish cost correct
    j records hj kind left a tail gap
  refine ⟨trace,hr,hl,?_⟩
  intro k
  have hs := PSTRTMTrace002.visitedSpace_le (originalToDestMachine route j kind) inputLength (trace.take k)
  have hk : (trace.take k).length≤trace.length := by simp only [List.length_take]; omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedLoad038
