module
public import Structure.PA17_TM_RatArithmetic_FirstRaw_052b
public import Structure.PA17_TM_RatArithmetic_FirstMul_051c

/-! Concrete original-input first multiplication. The complete frozen051
package supplies the actual consumer run and its original-input resources. -/
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstRaw052
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticParse002
open PA17TMRatArithmeticMulStart049 PA17TMRatArithmeticFirstMul051
open PA17TMRatArithmeticMulFields048 PA17TMRatArithmeticPairInput050
open PA17TMRatArithmeticWideCache045
attribute [local implicit_reducible] stageCap mulStartCap commonCap bridgeCap cycleCap

def firstCap : Nat := bridgeCap allocationK (cycleCap 63)
attribute [local implicit_reducible] firstCap
def firstMachine : Machine firstCap :=
  bridgeMachine allocationK (cycleMachine 63 .nx .ny) (cycleEntry 63)
def firstFinal (x y : Rat) (newGap : Nat) : MachineState firstCap :=
  consumerState allocationK (cycleCap 63) (cyclePort 63 (actualMemory x y))
    (firstCycleOutput x y [false] newGap)

def firstTimeC : Nat := 16*allocationK+533+32768*(allocationK+256)
def firstResourceC : Nat := 2*firstTimeC+2

private theorem input_power (i : Nat) : i+1≤(i+1)^4 := by
  simpa only [pow_one] using Nat.pow_le_pow_right
    (Nat.succ_le_succ (Nat.zero_le i)) (by decide : (1 : Nat) ≤ 4)

private theorem coefficient_comparison (c : Nat) : c≤2*c+2 ∧ 2*c+1≤2*c+2 := by
  constructor
  · omega
  · omega

private theorem time_sum (n : Nat) :
    (16*allocationK+533)*n^4+32768*(allocationK+256)*n^4=firstTimeC*n^4 := by
  unfold firstTimeC
  ring

private theorem space_sum (c n : Nat) : n+2*(c*n)=(2*c+1)*n := by ring

theorem firstFinal_tape (x y : Rat) (newGap : Nat) :
    (firstFinal x y newGap).Tape=firstCycleOutput x y [false] newGap := rfl

theorem firstFinal_label (x y : Rat) (newGap : Nat) :
    (firstFinal x y newGap).q.val=commonCap allocationK (cycleCap 63)+1+
      (2079*(actualMemory x y).val+2078) := by
  unfold firstFinal
  rw [consumerState_label,cyclePort_value]

/-- The original codec begins at actual numeric0. The fixed049 frontend,
one real finite dispatch and the actual051 multiplication are ONE trace.
The product is a physically stored canonical M record, not an input answer. -/
theorem original_first_mul_runs (x y : Rat) :
    ∃ newGap trace, 6≤newGap ∧ newGap≤2*allocationK*(fieldWidth x y)^2 ∧
      Runs firstMachine (encode [.rational x,.rational y]) trace (firstFinal x y newGap) ∧
      trace.length≤firstTimeC*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨newGap,tailTrace,lower,upper,run,time,_space⟩ := firstCycle64_polynomial_contract x y [false]
  have input : firstMInput x y [false] (allocationK*(fieldWidth x y)^2)=
      (originalFinal allocationK x y).Tape := by
    rw [firstMInput_allocator]
    rfl
  rw [input] at run
  have callee : PSTRTMSeq005.RunsFrom (cycleMachine 63 .nx .ny)
      ⟨cycleEntry 63 (actualMemory x y),(originalFinal allocationK x y).Tape⟩ tailTrace
      ⟨cyclePort 63 (actualMemory x y),firstCycleOutput x y [false] newGap⟩ := run
  obtain ⟨trace,hr,hl⟩ := combine_actual allocationK (cycleMachine 63 .nx .ny) (cycleEntry 63) x y _ _ callee
  let i := (encode [.rational x,.rational y]).length
  have hw : (fieldWidth x y+1)^4≤(i+1)^4 :=
    Nat.pow_le_pow_left (Nat.add_le_add_right (original_width_le_input x y) 1) 4
  have hp : (i+1)^3≤(i+1)^4 := Nat.pow_le_pow_right
    (Nat.succ_le_succ (Nat.zero_le i)) (by decide : (3 : Nat) ≤ 4)
  have prefixFee := Nat.mul_le_mul_left (16*allocationK+533) hw
  have calleeFee := time.trans (Nat.mul_le_mul_left (32768*(allocationK+256)) hp)
  refine ⟨newGap,trace,lower,upper,hr,?_⟩
  change trace.length≤firstTimeC*(i+1)^4
  calc
    _ ≤ (16*allocationK+533)*(fieldWidth x y+1)^4+tailTrace.length := hl
    _ ≤ (16*allocationK+533)*(i+1)^4+32768*(allocationK+256)*(i+1)^4 := Nat.add_le_add prefixFee calleeFee
    _ = firstTimeC*(i+1)^4 := time_sum _

theorem original_first_mul_contract (x y : Rat) :
    ∃ newGap trace, 6≤newGap ∧ newGap≤2*allocationK*(fieldWidth x y)^2 ∧
      Runs firstMachine (encode [.rational x,.rational y]) trace (firstFinal x y newGap) ∧
      trace.length≤firstResourceC*((encode [.rational x,.rational y]).length+1)^4 ∧
      ∀ prefixLength, visitedSpace firstMachine (encode [.rational x,.rational y]).length (trace.take prefixLength)≤
        firstResourceC*((encode [.rational x,.rational y]).length+1)^4 := by
  obtain ⟨newGap,trace,lower,upper,hr,ht⟩ := original_first_mul_runs x y
  let i := (encode [.rational x,.rational y]).length
  have timeBound : trace.length≤firstTimeC*(i+1)^4 := ht
  have hi := input_power i
  have hc : firstTimeC≤firstResourceC := (coefficient_comparison firstTimeC).1
  refine ⟨newGap,trace,lower,upper,hr,ht.trans (Nat.mul_le_mul_right _ hc),?_⟩
  intro prefixLength
  have hs := PSTRTMTrace002.visitedSpace_le firstMachine i (trace.take prefixLength)
  have hl : (trace.take prefixLength).length≤trace.length := by
    rw [List.length_take]
    exact Nat.min_le_right _ _
  change visitedSpace firstMachine i (trace.take prefixLength)≤firstResourceC*(i+1)^4
  calc
    _ ≤ i+2*(trace.take prefixLength).length+1 := hs
    _ ≤ i+2*(firstTimeC*(i+1)^4)+1 :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left 2 (hl.trans timeBound)) i) 1
    _ = (i+1)+2*(firstTimeC*(i+1)^4) := by ac_rfl
    _ ≤ (i+1)^4+2*(firstTimeC*(i+1)^4) := Nat.add_le_add_right hi _
    _ = (2*firstTimeC+1)*(i+1)^4 := space_sum _ _
    _ ≤ firstResourceC*(i+1)^4 := Nat.mul_le_mul_right _ (coefficient_comparison firstTimeC).2

/-- Fixed code and positive polynomial constants BEFORE every original
pair. No memory, room, allocation, native value or callee run is supplied. -/
theorem original_first_mul_exists :
    ∃ states c d : Nat, ∃ program : Machine states, 0<c ∧ 0<d ∧
      ∀ x y : Rat, ∃ newGap trace final,
        6≤newGap ∧ newGap≤2*allocationK*(fieldWidth x y)^2 ∧
        Runs program (encode [.rational x,.rational y]) trace final ∧
        final.Tape=firstCycleOutput x y [false] newGap ∧
        final.q.val=commonCap allocationK (cycleCap 63)+1+(2079*(actualMemory x y).val+2078) ∧
        trace.length≤c*((encode [.rational x,.rational y]).length+1)^d ∧
        ∀ prefixLength, visitedSpace program (encode [.rational x,.rational y]).length (trace.take prefixLength)≤
          c*((encode [.rational x,.rational y]).length+1)^d := by
  refine ⟨firstCap,firstResourceC,4,firstMachine,by unfold firstResourceC;positivity,by decide,?_⟩
  intro x y
  obtain ⟨newGap,trace,lower,upper,hr,ht,hs⟩ := original_first_mul_contract x y
  exact ⟨newGap,trace,firstFinal x y newGap,lower,upper,hr,firstFinal_tape _ _ _,firstFinal_label _ _ _,ht,hs⟩

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFirstRaw052
