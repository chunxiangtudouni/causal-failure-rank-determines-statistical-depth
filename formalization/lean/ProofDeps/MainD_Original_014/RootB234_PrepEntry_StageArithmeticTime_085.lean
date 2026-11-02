module

public import RootB234_PrepEntry_StageArithmeticRun_084

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageArithmetic
open Turing PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM RootB234.PrepExponent RootL01.SymbolicSource
variable {C : Type*}

def nativeCoefficient : Nat := max RatMulDiv.mulCoefficient RatAddSub.addSubCoefficient
def chosenCoefficient (multiply : Bool) : Nat := if multiply then RatMulDiv.mulCoefficient else RatAddSub.addSubCoefficient
def workCoefficient : Nat := 16*8192+nativeCoefficient*(16*8192+1)^4+8
def binaryCoefficient : Nat := 9+7*workCoefficient+128
def restoreCoefficient : Nat := 16*(24+2*workCoefficient)+1
def timeCoefficient : Nat := 32+binaryCoefficient+32*restoreCoefficient

def rawBank (before : Bank) : Bank := QLoop.rawBackground (StageStash.stashBank before 8) (before 7) (before 11)
def nativeSpace (multiply : Bool) (before : Bank) (x y : Rat) (tail : List Bool) : Nat :=
  RatBinary.space (chosenCoefficient multiply) (rawBank before) x y tail (before 7)

theorem chosen_le (multiply : Bool) : chosenCoefficient multiply≤nativeCoefficient := by
  cases multiply with
  | false => exact Nat.le_max_right _ _
  | true => exact Nat.le_max_left _ _

theorem scale_positive (before : Bank) : 1≤StageStash.scale before := by unfold StageStash.scale;omega

theorem point_bound (before : Bank) (slot : Stack) : (before slot).length≤StageStash.scale before :=
  (StageStash.point_mass before slot).trans (Nat.le_add_right _ _)

theorem stash_length (before : Bank) (slot : Stack) :
    (StageStash.stashBank before 8 slot).length≤17*StageStash.scale before := by
  by_cases zero : slot=0
  · subst slot
    rw [StageStash.stash_spool,StageStash.spool_length]
    have fields:=StageStash.fieldMass_bound before 8
    have head:=StageStash.point_mass before 0
    unfold StageStash.scale
    omega
  · simp only [StageStash.stashBank,zero,ite_false]
    split_ifs
    · exact Nat.zero_le _
    · have bound:=point_bound before slot;omega

theorem raw_length (before : Bank) (slot : Stack) : (rawBank before slot).length≤17*StageStash.scale before := by
  unfold rawBank QLoop.rawBackground StackIso.slots QLoop.bank
  split_ifs
  all_goals first
  | exact Nat.zero_le _
  | exact stash_length before _
  | have a:=point_bound before 7;omega
  | have a:=point_bound before 11;omega

theorem raw_mass (before : Bank) : RatInput.occupied (rawBank before)≤272*StageStash.scale before := by
  exact (RatInput.Encoder.occupied_bound _ _ (raw_length before)).trans_eq (by ring)

theorem fields_bound (before : Bank) (x y : Rat) (tail : List Bool) (source : before 15=RatPair.input x y tail) :
    RatPair.fieldSize x y≤StageStash.scale before ∧ tail.length≤StageStash.scale before := by
  have bound:=point_bound before 15
  rw [source] at bound
  simp only [RatPair.input,RatPair.packet,List.length_append,RatInput.Encoder.packet_length,List.length_nil,Nat.add_zero] at bound
  have sizes:=RatBinary.fieldSize_eq x y
  omega

theorem pair_space_bound (before : Bank) (x y : Rat) (tail : List Bool) (source : before 15=RatPair.input x y tail) :
    RatPair.space (rawBank before) x y tail (before 7)≤8192*StageStash.scale before := by
  have mass:=raw_mass before
  have outside : RatPair.Link.outside (rawBank before)≤RatInput.occupied (rawBank before) := by
    apply Finset.sum_le_sum
    intro slot _
    split_ifs <;> omega
  have sizes:=fields_bound before x y tail source
  have scratch:=point_bound before 7
  have positive:=scale_positive before
  change RatPair.Link.outside (rawBank before)+tail.length+(before 7).length+
    258*RatPair.fieldSize x y+2572≤_
  omega

theorem nativeSpace_bound (multiply : Bool) (before : Bank) (x y : Rat) (tail : List Bool)
    (source : before 15=RatPair.input x y tail) :
    nativeSpace multiply before x y tail≤workCoefficient*(StageStash.scale before)^4 := by
  let S:=StageStash.scale before
  let P:=RatPair.space (rawBank before) x y tail (before 7)
  have positive : 1≤S:=scale_positive before
  have power : S≤S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤4)
  have one : 1≤S^4:=positive.trans power
  have pairBound : P≤8192*S:=pair_space_bound before x y tail source
  have args : 16*P+1≤(16*8192+1)*S := by omega
  have fourth:=Nat.pow_le_pow_left args 4
  rw [Nat.mul_pow] at fourth
  have raw:=Nat.mul_le_mul (chosen_le multiply) fourth
  change chosenCoefficient multiply*(16*P+1)^4≤nativeCoefficient*((16*8192+1)^4*S^4) at raw
  change 16*P+chosenCoefficient multiply*(16*P+1)^4+8≤workCoefficient*S^4
  unfold workCoefficient
  nlinarith only [raw,pairBound,power,one]

theorem binaryTime_bound (multiply : Bool) (before : Bank) (x y : Rat) (tail : List Bool)
    (source : before 15=RatPair.input x y tail) :
    binaryTime multiply (StageStash.stashBank before 8) (before 7) (before 11) x y tail≤
      binaryCoefficient*(StageStash.scale before)^4 := by
  have space:=nativeSpace_bound multiply before x y tail source
  have fields:=(fields_bound before x y tail source).1
  have positive:=scale_positive before
  have power : StageStash.scale before≤(StageStash.scale before)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤4)
  have one : 1≤(StageStash.scale before)^4:=positive.trans power
  have formula : binaryTime multiply (StageStash.stashBank before 8) (before 7) (before 11) x y tail=
      9*RatPair.fieldSize x y+7*nativeSpace multiply before x y tail+128 := by
    cases multiply <;> rfl
  rw [formula]
  unfold binaryCoefficient
  nlinarith only [space,fields,power,one]

/-- This numerical size lemma extracts a fact from an existing concrete
binary callee. It does not add an execution, allocate a packet, or change
the selected enclosing run. -/
theorem result_field_bound (multiply : Bool) (before : Bank) (memory : Store C) (x y : Rat) (tail : List Bool) :
    RatInput.Encoder.fieldSize (result multiply x y)≤nativeSpace multiply before x y tail := by
  cases multiply with
  | true =>
    let m:=QLoop.rawMemory memory
    obtain ⟨run,final,facts,_⟩:=Arithmetic.actual_mul (rawBank before) m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
      m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail (before 7)
    have source : final.stk 15=RatInput.Encoder.packet (x*y) tail := by rw [facts.contents];rfl
    exact (RatBinary.result_field_bound final.stk (x*y) tail source).trans
      (facts.boundaries final (List.mem_of_getLast? facts.last)).1
  | false =>
    let m:=subMemory memory
    obtain ⟨run,final,facts,_⟩:=Arithmetic.actual_sub (rawBank before) m.1.1.1.1.1 m.1.1.1.1.2.1 m.1.1.1.1.2.2
      m.1.1.1.2 m.1.1.2 m.1.2 m.2 x y tail (before 7)
    have source : final.stk 15=RatInput.Encoder.packet (x-y) tail := by rw [facts.contents];rfl
    exact (RatBinary.result_field_bound final.stk (x-y) tail source).trans
      (facts.boundaries final (List.mem_of_getLast? facts.last)).1

theorem restore_scale_bound (multiply : Bool) (before : Bank) (memory : Store C) (x y : Rat) (tail : List Bool)
    (source : before 15=RatPair.input x y tail) :
    StageStash.scale (output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail))≤
      restoreCoefficient*(StageStash.scale before)^4 := by
  have positive:=scale_positive before
  have power : StageStash.scale before≤(StageStash.scale before)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤4)
  have one : 1≤(StageStash.scale before)^4:=positive.trans power
  have resultSize:=(result_field_bound multiply before memory x y tail).trans (nativeSpace_bound multiply before x y tail source)
  have tailSize:=(fields_bound before x y tail source).2
  have each : ∀ slot,(output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail) slot).length≤
      (24+2*workCoefficient)*(StageStash.scale before)^4 := by
    intro slot
    by_cases same : slot=15
    · subst slot
      rw [output,Function.update_self,RatInput.Encoder.packet_length]
      nlinarith only [resultSize,tailSize,power,one]
    · rw [output,Function.update_of_ne same]
      have bound:=stash_length before slot
      nlinarith only [bound,power,Nat.zero_le (workCoefficient*(StageStash.scale before)^4)]
  have mass:=StageStash.occupied_bound _ _ each
  change StageStash.mass (output (StageStash.stashBank before 8) (RatInput.Encoder.packet (result multiply x y) tail))+1≤
    restoreCoefficient*(StageStash.scale before)^4
  unfold restoreCoefficient
  nlinarith only [mass,one]

theorem actualCost_bound (multiply : Bool) (before : Bank) (memory : Store C) (x y : Rat) (tail : List Bool)
    (source : before 15=RatPair.input x y tail) :
    actualCost multiply before x y tail≤timeCoefficient*(StageStash.scale before)^4 := by
  have binaryCap:=binaryTime_bound multiply before x y tail source
  have restoreCap:=restore_scale_bound multiply before memory x y tail source
  have power : StageStash.scale before≤(StageStash.scale before)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (scale_positive before) (by decide : 1≤4)
  unfold actualCost timeCoefficient
  nlinarith only [binaryCap,restoreCap,power]

end RootB234.PrepEntry.StageArithmetic
