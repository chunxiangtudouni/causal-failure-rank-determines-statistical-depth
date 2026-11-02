module

public import B23_4_RatWordPrep_SeqCmp_WordCanonicalMass_145
public import B23_4_RatWordPrep_SeqCmp_WordBinaryDataBounds_147

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

structure PlanData (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) (data : Data) : Prop where
  small : ∀ slot,slot=0 ∨ slot=1 ∨ slot=15→
    (data slot).length≤7 ∧ ∀ q∈data slot,q∈operands E target word
  table : ∃ front,data 2=front++Channels.channelValues E ∧ front.length≤7 ∧
    ∀ q∈front,q∈operands E target word

def planScale (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  frameMass frame+2*(wordInput E target word).length+
    28*(16*((wordInput E target word).length+1)^2+6)+1

def planCoefficient : Nat :=
  10000*(binaryScaleCoefficient RatMulDiv.divCoefficient+binaryScaleCoefficient RatAddSub.addSubCoefficient+
    RootB234.RatPacketTransport.coefficient+1)

def planBudget (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) : Nat :=
  planCoefficient*(planScale frame E target word)^4

theorem planScale_pos (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord) :
    1≤planScale frame E target word := by unfold planScale; omega

theorem PlanData.scale_bound {E : BinaryExperiment} {target : Rat} {word : E.StoppedWord} {data : Data}
    (capacity : PlanData E target word data) (frame : RatInput.Stack → List Bool) (before : State C)
    (shape : before.stk=layout frame data) : scale before≤planScale frame E target word := by
  have fields := operands_field_bound E target word
  have mass := canonical_mass frame data (Channels.channelValues E)
    (8*((wordInput E target word).length+1)^2) 7 (by
      intro slot selected
      exact ⟨(capacity.small slot selected).1,by
        intro q member
        exact fields q ((capacity.small slot selected).2 q member)⟩) (by
      obtain ⟨front,split,size,members⟩ := capacity.table
      exact ⟨front,split,size,by intro q member; exact fields q (members q member)⟩)
  have tableSize := channel_packets_le_input E target word
  unfold scale planScale
  rw [shape]
  nlinarith

theorem plan_field_bound (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat)
    (word : E.StoppedWord) (x : Rat) (member : x∈operands E target word) :
    RatInput.Encoder.fieldSize x≤planScale frame E target word := by
  have bound := operands_field_bound E target word x member
  unfold planScale
  omega

theorem packet_plan_bounds {caller : Statement C} {before final : State C} {run : Segment caller before final}
    (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (data : Data) (capacity : PlanData E target word data) (shape : before.stk=layout frame data)
    (x : Rat) (member : x∈operands E target word)
    (bounds : RunBounds caller run (3*RatInput.Encoder.fieldSize x+14)
      (RootB234.RatPacketTransport.coefficient*scale before) (RootB234.RatPacketTransport.coefficient*scale before)) :
    RunBounds caller run (planBudget frame E target word) (planBudget frame E target word) (planBudget frame E target word) := by
  have s := capacity.scale_bound frame before shape
  have positive := planScale_pos frame E target word
  have power := SeqCmp.linear_fourth _ positive
  have field := plan_field_bound frame E target word x member
  have constant : RootB234.RatPacketTransport.coefficient≤planCoefficient := by unfold planCoefficient; omega
  have timeConstant : 17≤planCoefficient := by unfold planCoefficient; omega
  have time : 3*RatInput.Encoder.fieldSize x+14≤planBudget frame E target word := by
    calc
      _≤17*(planScale frame E target word)^4 := by omega
      _≤planCoefficient*(planScale frame E target word)^4 := Nat.mul_le_mul_right _ timeConstant
  have workspace : RootB234.RatPacketTransport.coefficient*scale before≤planBudget frame E target word :=
    Nat.mul_le_mul constant (s.trans power)
  exact bounds.mono time workspace workspace

theorem one_plan_bounds {caller : Statement C} {before final : State C} {run : Segment caller before final}
    (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (data : Data) (capacity : PlanData E target word data) (shape : before.stk=layout frame data)
    (bounds : RunBounds caller run 2 (scale before+10) (20*(scale before+11))) :
    RunBounds caller run (planBudget frame E target word) (planBudget frame E target word) (planBudget frame E target word) := by
  have s := capacity.scale_bound frame before shape
  have positive := planScale_pos frame E target word
  have power := SeqCmp.linear_fourth _ positive
  have one : 1≤(planScale frame E target word)^4 := positive.trans power
  have constant : 240≤planCoefficient := by unfold planCoefficient; omega
  have time : 2≤planBudget frame E target word := by
    have small : 2≤planCoefficient := by omega
    simpa only [Nat.mul_one,planBudget] using Nat.mul_le_mul small one
  have workspace : scale before+10≤planBudget frame E target word := by
    calc
      _≤11*(planScale frame E target word)^4 := by omega
      _≤planCoefficient*(planScale frame E target word)^4 := Nat.mul_le_mul_right _ (by omega)
  have clock : 20*(scale before+11)≤planBudget frame E target word := by
    calc
      _≤240*(planScale frame E target word)^4 := by omega
      _≤planCoefficient*(planScale frame E target word)^4 := Nat.mul_le_mul_right _ constant
  exact bounds.mono time workspace clock

theorem native_plan_bounds {caller : Statement C} {before final : State C} {run : Segment caller before final}
    (frame : RatInput.Stack → List Bool) (E : BinaryExperiment) (target : Rat) (word : E.StoppedWord)
    (data : Data) (capacity : PlanData E target word data) (shape : before.stk=layout frame data)
    (coefficient : Nat) (choice : coefficient=RatMulDiv.divCoefficient ∨ coefficient=RatAddSub.addSubCoefficient)
    (bounds : RunBounds caller run ((7*binaryScaleCoefficient coefficient+137)*(scale before)^4)
      ((binaryScaleCoefficient coefficient+32)*(scale before)^4)
      ((64*(binaryScaleCoefficient coefficient+33))*(scale before)^4)) :
    RunBounds caller run (planBudget frame E target word) (planBudget frame E target word) (planBudget frame E target word) := by
  have s := Nat.pow_le_pow_left (capacity.scale_bound frame before shape) 4
  have time : 7*binaryScaleCoefficient coefficient+137≤planCoefficient := by
    rcases choice with rfl | rfl <;> unfold planCoefficient <;> omega
  have space : binaryScaleCoefficient coefficient+32≤planCoefficient := by
    rcases choice with rfl | rfl <;> unfold planCoefficient <;> omega
  have clock : 64*(binaryScaleCoefficient coefficient+33)≤planCoefficient := by
    rcases choice with rfl | rfl <;> unfold planCoefficient <;> omega
  exact bounds.mono (Nat.mul_le_mul time s) (Nat.mul_le_mul space s) (Nat.mul_le_mul clock s)

end B23_4_RatWordPrep.WordFinish.Resources
