module
public import Structure.PA17_TM_RatArithmetic_CachedPair_054c
public import Structure.PA17_TM_RatArithmetic_CachedPair_054e
public import Structure.PA17_TM_RatArithmetic_OutputFinish_044a
public import Structure.PA17_TM_RatArithmetic_FlagZero_028b

/-! Canonical metadata is obtained from actual native/store results; it
does not select the executable. In particular the real B-read exit has
the canonical field's physical first bit, while old128 carry is unchanged.
The final044 consumer takes BReady, and native055 takes the distinct plain
raw pair. Their physical input tapes are exposed without a free head move. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticCachedLoad038
open PA17TMRatArithmeticFarLoad031
attribute [local implicit_reducible] cachedReadyCap cachedPairCap cachedFirstCap selectedSharedCap
  selectedPlainCap locatorCap latestCap plainKernelCap sharedKernelCap totalStates

theorem canonical_head_tail (n : Nat) : PA17TMRatArithmeticPairEncode017.payload n=
    (PA17TMRatArithmeticPairEncode017.payload n).head!::(PA17TMRatArithmeticPairEncode017.payload n).tail := by
  have hn := PA17TMRatArithmeticFlagZero028.payload_ne_nil n
  cases h : PA17TMRatArithmeticPairEncode017.payload n with
  | nil => exact False.elim (hn h)
  | cons bit tail => rfl

theorem original_ready_final_geometry (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) (gap u v : Nat) :
    originalBReady sx [false] nxTail dxTail nyTail dyTail first records gap
      (PA17TMRatArithmeticPairEncode017.payload u) (PA17TMRatArithmeticPairEncode017.payload v)=
      PA17TMRatArithmeticOutputFinish044.pairInput gap
        (PA17TMRatArithmeticOutputFinish044.latestLeft sx (false::nxTail) dxTail (false::nyTail) dyTail first records) u v := by
  unfold originalBReady
  rw [originalBankLeft_home]
  rfl

theorem original_native_tail_geometry (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool)
    (first : RecordSpec) (records : List RecordSpec) (gap a b : Nat) :
    originalNativeInput sx counter nxTail dxTail nyTail dyTail first records gap a b=
      Tape.mk₂ (false::true::(List.replicate gap false++true::
        bankLeft (PA17TMRatArithmeticReturnHome037.firstLeft sx counter
          (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) first) records))
        (encodeNat a++encodeNat b) := by
  unfold originalNativeInput originalWorkArchive
  rw [originalBankLeft_home]

/-- The final output U/V pair, including U=0 and V=1, is selected from
real canonical stored records. SX/SY/Uzero are still opaque old carry;
this theorem does not pretend the final sign controller has executed. -/
theorem cached_ready_canonical_bounded (j aLater bLater : Nat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hj : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (sx : Bool) (nxTail dxTail nyTail dyTail : List Bool) (gap u v : Nat)
    (hu : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload u)
    (hv : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload v) :
    BoundedRun (cachedReadyRow j aLater bLater)
      (originalWorkHeader sx [false] nxTail dxTail nyTail dyTail first records gap)
      (cachedReadyPort j aLater bLater (PA17TMRatArithmeticPairEncode017.payload v).head!)
      (PA17TMRatArithmeticOutputFinish044.pairInput gap
        (PA17TMRatArithmeticOutputFinish044.latestLeft sx (false::nxTail) dxTail (false::nyTail) dyTail first records) u v)
      (cachedReadyFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap) := by
  have hdA := hu.trans (canonical_head_tail u)
  have hdB := hv.trans (canonical_head_tail v)
  have h := cached_ready_bounded j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
    hj hbankA haLater hbankB hbLater (PA17TMRatArithmeticPairEncode017.payload u).head!
    (PA17TMRatArithmeticPairEncode017.payload v).head! (PA17TMRatArithmeticPairEncode017.payload u).tail
    (PA17TMRatArithmeticPairEncode017.payload v).tail hdA hdB sx [false] nxTail dxTail nyTail dyTail gap
  rw [hu,hv,original_ready_final_geometry] at h
  exact h

theorem cached_pair_canonical_bounded (j aLater bLater : Nat) (first : RecordSpec)
    (records beforeA : List RecordSpec) (sourceA : RecordSpec) (followingA beforeB : List RecordSpec)
    (sourceB : RecordSpec) (followingB : List RecordSpec) (hj : records.length=j)
    (hbankA : beforeA++sourceA::followingA=first::records) (haLater : followingA.length=aLater)
    (hbankB : beforeB++sourceB::followingB=first::records) (hbLater : followingB.length=bLater)
    (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat)
    (ha : sourceA.digits=PA17TMRatArithmeticPairEncode017.payload a)
    (hb : sourceB.digits=PA17TMRatArithmeticPairEncode017.payload b) :
    BoundedRun (cachedPairRow j aLater bLater)
      (originalWorkHeader sx counter nxTail dxTail nyTail dyTail first records gap) (cachedPairPort j aLater bLater)
      (originalNativeInput sx counter nxTail dxTail nyTail dyTail first records gap a b)
      (cachedPairFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap a b) :=
  cached_pair_bounded j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
    hj hbankA haLater hbankB hbLater (PA17TMRatArithmeticPairEncode017.payload a).head!
    (PA17TMRatArithmeticPairEncode017.payload b).head! (PA17TMRatArithmeticPairEncode017.payload a).tail
    (PA17TMRatArithmeticPairEncode017.payload b).tail (ha.trans (canonical_head_tail a))
    (hb.trans (canonical_head_tail b)) sx counter nxTail dxTail nyTail dyTail gap a b ha hb

def cachedPairTime (j aLater bLater : Nat) (first : RecordSpec) (records beforeA : List RecordSpec)
    (sourceA : RecordSpec) (followingA beforeB : List RecordSpec) (sourceB : RecordSpec)
    (followingB : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat) : Nat :=
  locatorFee (j+1) aLater nxTail dxTail nyTail dyTail beforeA sourceA followingA+
    cachedPlainTime aLater followingA (sourceA.digits.tail.length+1) gap+
    originalHomeFee j first records nxTail dxTail nyTail dyTail gap+
    locatorFee (j+1) bLater nxTail dxTail nyTail dyTail beforeB sourceB followingB+
    cachedSharedTime bLater followingB (sourceB.digits.tail.length+1) sourceA.digits.length gap+
    64*((PA17TMRatArithmeticPairEncode017.payload a).length+
      (PA17TMRatArithmeticPairEncode017.payload b).length+1)^2

theorem cached_pair_fee_le (j aLater bLater : Nat) (first : RecordSpec) (records beforeA : List RecordSpec)
    (sourceA : RecordSpec) (followingA beforeB : List RecordSpec) (sourceB : RecordSpec)
    (followingB : List RecordSpec) (nxTail dxTail nyTail dyTail : List Bool) (gap a b : Nat) :
    cachedPairFee j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap a b≤
      cachedPairTime j aLater bLater first records beforeA sourceA followingA beforeB sourceB followingB
        nxTail dxTail nyTail dyTail gap a b := by
  have ha := cached_plain_time_le aLater followingA sourceA.digits.tail gap
  have hb := cached_shared_time_le bLater followingB sourceB.digits.tail sourceA.digits gap
  simp only [List.length_cons] at ha hb
  unfold cachedPairFee cachedReadyFee cachedFirstFee selectedPlainFee selectedSharedFee cachedPairTime
  omega

theorem cached_ready_carry_preserved (p j aLater bLater : Nat) (memory : Fin (p+1)) (actualBitB : Bool) :
    phaseOf (label memory (cachedReadyPort j aLater bLater actualBitB))=memory := phaseOf_label _ _

theorem cached_pair_carry_preserved (p j aLater bLater : Nat) (memory : Fin (p+1)) :
    phaseOf (label memory (cachedPairPort j aLater bLater))=memory := phaseOf_label _ _

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPair054
