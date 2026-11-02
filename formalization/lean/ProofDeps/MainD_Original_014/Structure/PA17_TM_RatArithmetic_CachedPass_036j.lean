module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036i

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticBankWalk033

/-- Fixed j/k code, no source width, counter, record value or answer
inputs. The entire source/cache bank and h are kept; only the actual far
zero gap grows. The final head is physically the original input header. -/
theorem cached_pass_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (sx : Bool) (h n : Nat) (nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (s:=cachedPassCap j k) (cachedPassMachine j k)
      (Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones h))
        (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) (cachedTail records n)))
      (Fin.last (cachedPassCap j k))
      (Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
        (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
          (cachedTail records (n+k*bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail))))))
      (cachedPassFee j k records (bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)) n) := by
  have hr := (raw_cached_pass_bounded j k records hj sx h n nxTail dxTail nyTail dyTail).pad
    (Nat.le_of_eq (rawCachedPassCap_eq j k))
  have hq : padLabel (Nat.le_of_eq (rawCachedPassCap_eq j k)) (Fin.last (rawCachedPassCap j k))=
      Fin.last (cachedPassCap j k) := by
    apply Fin.ext
    exact rawCachedPassCap_eq j k
  rw [hq] at hr
  exact hr

theorem original_cached_pass_bounded (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (h n : Nat) (x y : Rat) :
    BoundedRun (s:=cachedPassCap j k) (cachedPassMachine j k)
      (Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones h))
        (originalBank x y (cachedTail records n))) (Fin.last (cachedPassCap j k))
      (Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
        (prefixRight (sign x) (originalBank x y (cachedTail records (n+k*fieldWidth x y)))))
      (cachedPassFee j k records (fieldWidth x y) n) := by
  have hr := cached_pass_bounded j k records hj (sign x) h n (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail
  change BoundedRun (s:=cachedPassCap j k) (cachedPassMachine j k)
    (Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones h))
      (originalBank x y (cachedTail records n))) (Fin.last (cachedPassCap j k))
    (Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
      (prefixRight (sign x) (originalBank x y (cachedTail records (n+k*bankWidth
        (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
        (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y)))))))
    (cachedPassFee j k records (bankWidth (clampFirst (numeratorDigits x)) (clampFirst (denominatorDigits x))
      (clampFirst (numeratorDigits y)) (clampFirst (denominatorDigits y))) n) at hr
  rw [originalWidth_eq] at hr
  exact hr

/-- The SAME actual body trace pays every cache traversal and expansion.
The charged initial space here is the original unqualified two-Rat input. -/
theorem original_cached_pass_contract (j k : Nat) (records : List RecordSpec) (hj : records.length=j)
    (h n : Nat) (x y : Rat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (cachedPassMachine j k)
      ⟨0,Tape.mk₂ (false::nxContext (sign x) (false::ROOTTMGCDCounter011.ones h))
        (originalBank x y (cachedTail records n))⟩ trace
      ⟨Fin.last (cachedPassCap j k),Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
        (prefixRight (sign x) (originalBank x y (cachedTail records (n+k*fieldWidth x y))))⟩ ∧
      trace.length≤cachedPassFee j k records (fieldWidth x y) n ∧
      ∀ prefixLength, visitedSpace (cachedPassMachine j k) (encode [.rational x,.rational y]).length
        (trace.take prefixLength) ≤
        (encode [.rational x,.rational y]).length+2*cachedPassFee j k records (fieldWidth x y) n+1 := by
  obtain ⟨trace,hr,hl⟩ := original_cached_pass_bounded j k records hj h n x y
  refine ⟨trace,hr,hl,?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le (cachedPassMachine j k)
    (encode [.rational x,.rational y]).length (trace.take prefixLength)
  have hp : (trace.take prefixLength).length≤trace.length := by simp only [List.length_take];omega
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
