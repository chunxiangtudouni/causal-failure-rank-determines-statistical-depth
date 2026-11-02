module
public import Structure.PA17_TM_RatArithmetic_Sign_003a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSign003

theorem encodeNat_zero : encodeNat 0 = [true,false,false] := by decide
theorem encodeNat_one : encodeNat 1 = [true,false,true] := by decide

theorem natBits_ge_two (n : Nat) (hn : n ≠ 0) (ho : n ≠ 1) : 2 ≤ natBits n := by
  have hp : 1 ≤ natBits n := by unfold natBits; omega
  have hb := PSTRTMCodec001.natBits_bound n
  by_contra h
  have hw : natBits n = 1 := by omega
  rw [hw] at hb
  norm_num at hb
  omega

def wideRest (n : Nat) : List Bool :=
  List.replicate (natBits n-2) true ++ [false] ++
    List.ofFn (fun position : Fin (natBits n) => n.testBit position.val)

theorem encodeNat_wide (n : Nat) (hn : n ≠ 0) (ho : n ≠ 1) :
    encodeNat n = true::true::wideRest n := by
  have hb := natBits_ge_two n hn ho
  have hh : natBits n = 2+(natBits n-2) := by omega
  have hr : List.replicate (natBits n) true = true::true::List.replicate (natBits n-2) true := by
    calc
      _ = List.replicate (2+(natBits n-2)) true := congrArg (fun k => List.replicate k true) hh
      _ = _ := by rw [List.replicate_add]; rfl
  simp only [encodeNat,hr,List.cons_append,wideRest]

def changedSign (n : Nat) (sign : Bool) : Bool := if n = 0 then false else !sign

def natTrace (n : Nat) (sign : Bool) (left tail : List Bool) : List (MachineState 15) :=
  if n = 0 then smallTrace sign false left tail
  else if n = 1 then smallTrace sign true left tail
  else wideTrace sign left (wideRest n ++ tail)

theorem nat_runsFrom (n : Nat) (sign : Bool) (left tail : List Bool) :
    PSTRTMSeq005.RunsFrom negateDatumMachine
      (state 0 left (true::sign::(encodeNat n ++ tail))) (natTrace n sign left tail)
      (state 15 left (true::changedSign n sign::(encodeNat n ++ tail))) := by
  by_cases hz : n = 0
  · subst n
    simpa only [natTrace,ite_true,changedSign,encodeNat_zero,List.cons_append,List.nil_append,smallSign,Bool.false_and] using
      small_runsFrom sign false left tail
  · by_cases ho : n = 1
    · subst n
      simpa only [natTrace,hz,ite_false,ite_true,changedSign,encodeNat_one,List.cons_append,List.nil_append,smallSign,Bool.true_and] using
        small_runsFrom sign true left tail
    · simpa only [natTrace,hz,ho,ite_false,changedSign,encodeNat_wide n hz ho,List.cons_append] using
        wide_runsFrom sign left (wideRest n ++ tail)

theorem natTrace_length_le (n : Nat) (sign : Bool) (left tail : List Bool) :
    (natTrace n sign left tail).length ≤ 10 := by
  unfold natTrace
  split
  · rw [smallTrace_length]
  · split
    · rw [smallTrace_length]
    · rw [wideTrace_length]; omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticSign003
