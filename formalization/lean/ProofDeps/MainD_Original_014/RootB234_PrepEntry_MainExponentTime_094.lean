module

public import RootB234_PrepEntry_MainExponentChannels_093
public import RootB234_PrepExponent_GlobalPublic044

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.MainExponent
open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM B23_4_RatWordPrep RootB234.PrepExponent RootL01.SymbolicSource
variable {I : Instance}

def dataCoefficient : Nat := 16*(2*Budget.coefficient+32)

theorem metadata_mass_bound (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    RatInput.occupied (metadataBank (preparationInput input contract budget) I.stageCount I.toolCount budget)≤
      Budget.coefficient*(arithmeticScale input contract budget)^3 := by
  exact (WholeChannels.output_mass_le input contract budget).trans (Nat.mul_le_mul_left Budget.coefficient
    (Nat.pow_le_pow_left (Budget.length_le_arithmeticScale input contract budget) 3))

theorem budget_field_bound (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    RatInput.Encoder.fieldSize budget≤Budget.coefficient*(arithmeticScale input contract budget)^3 := by
  have point:=RatInput.Encoder.point_mass (metadataBank (preparationInput input contract budget) I.stageCount I.toolCount budget) 15
  change (RatInput.Encoder.packet budget []).length≤_ at point
  rw [RatInput.Encoder.packet_length] at point
  have mass:=metadata_mass_bound input contract budget
  omega

theorem stage_count_bound (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    I.stageCount≤arithmeticScale input contract budget := by
  dsimp only [arithmeticScale,inputSize]
  omega

theorem data_bounds (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    RatInput.occupied (exponentBank (preparationInput input contract budget) I.stageCount I.toolCount budget)≤
      dataCoefficient*(arithmeticScale input contract budget)^3 ∧
    RatInput.occupied (stageBank (preparationInput input contract budget) I.stageCount I.toolCount budget)≤
      dataCoefficient*(arithmeticScale input contract budget)^3 ∧
    (movedBank (preparationInput input contract budget) I.stageCount I.toolCount budget 7).length≤
      dataCoefficient*(arithmeticScale input contract budget)^3 := by
  let S:=arithmeticScale input contract budget
  let H:=S^3
  let bits:=preparationInput input contract budget
  have positive : 1≤S := by dsimp only [S,arithmeticScale];omega
  have linear : S≤H := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤3)
  have one : 1≤H:=positive.trans linear
  have mass : RatInput.occupied (metadataBank bits I.stageCount I.toolCount budget)≤Budget.coefficient*H :=
    metadata_mass_bound input contract budget
  have each : ∀ slot,(metadataBank bits I.stageCount I.toolCount budget slot).length≤Budget.coefficient*H :=
    fun slot => (RatInput.Encoder.point_mass _ slot).trans mass
  have number : I.stageCount≤H := (stage_count_bound input contract budget).trans linear
  have computed : computedExponent (I:=I) budget≤H :=
    (RootB23.PrepScalar.original_global_exponent_bounded I input contract budget).trans linear
  have field : RatInput.Encoder.fieldSize budget≤Budget.coefficient*H:=budget_field_bound input contract budget
  have qField : RatInput.Encoder.fieldSize (Global.qValue I.stageCount)≤5+3*I.stageCount := RootB234.ECost.q_field I.stageCount
  have qBound : RatInput.Encoder.fieldSize (Global.qValue I.stageCount)≤8*H := by omega
  have eLength : (NatField.packet (BinaryExperiment.quotaExponent budget I.stageCount) []).length≤6*H := by
    rw [RootB234.ECost.natural_packet_length]
    have raw:=RootB234.ECost.raw_length (computedExponent (I:=I) budget)
    change (RootB234.ECost.raw (computedExponent (I:=I) budget)).length≤computedExponent (I:=I) budget+1 at raw
    change 2*(RootB234.ECost.raw (computedExponent (I:=I) budget)).length+2+[].length≤6*H
    simp only [List.length_nil]
    omega
  have cacheLength : (RatInput.Encoder.packet (Global.qValue I.stageCount) (RatInput.Encoder.packet budget [])).length≤
      (2*Budget.coefficient+28)*H := by
    rw [RatInput.Encoder.packet_length,RatInput.Encoder.packet_length]
    simp only [List.length_nil]
    nlinarith only [qBound,field,one]
  have eEach : ∀ slot,(exponentBank bits I.stageCount I.toolCount budget slot).length≤(2*Budget.coefficient+32)*H := by
    intro slot
    unfold exponentBank Global.bank
    split_ifs
    · nlinarith only [cacheLength,one]
    · nlinarith only [eLength,one]
    · have bound:=each 15
      change (RatInput.Encoder.packet budget []).length≤Budget.coefficient*H at bound
      nlinarith only [bound,one]
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · exact Nat.zero_le _
    · have bound:=each slot
      nlinarith only [bound,one]
  have sEach : ∀ slot,(stageBank bits I.stageCount I.toolCount budget slot).length≤(2*Budget.coefficient+32)*H := by
    intro slot
    by_cases same : slot=5
    · subst slot
      rw [stageBank,Function.update_self]
      nlinarith only [eLength,one]
    · rw [stageBank,Function.update_of_ne same]
      have bound:=each slot
      nlinarith only [bound,one]
  refine ⟨(RatInput.Encoder.occupied_bound _ _ eEach).trans_eq (by unfold dataCoefficient;ring),
    (RatInput.Encoder.occupied_bound _ _ sEach).trans_eq (by unfold dataCoefficient;ring),?_⟩
  change (RatInput.Encoder.packet (Global.qValue I.stageCount) (RatInput.Encoder.packet budget [])).length≤dataCoefficient*H
  unfold dataCoefficient
  nlinarith only [cacheLength,one]

/-- Fixed coefficients precede all original inputs. Every hypothesis of
the imported cost consumer is discharged by the actual metadata/layout
producer or the original scale definition. No cost/width/E premise is
passed to the original caller. -/
theorem time_polynomial :
    ∃ coefficient degree : Nat,0<coefficient ∧ 0<degree ∧
      ∀ (I : Instance) (input : StatisticalInput I) (contract : Contract I) (budget : Rat),
        time input contract budget≤coefficient*(arithmeticScale input contract budget)^degree := by
  obtain ⟨eCoefficient,eDegree,ePositive,dPositive,eBound⟩:=RootB234.ECost.original_scale_consumer Budget.coefficient 3
  let coefficient:=Budget.coefficient+eCoefficient+NatPacket.coefficient*(dataCoefficient+1)+
    (dataCoefficient+2)+StageChannels.coefficient*(dataCoefficient+1)^4
  let degree:=eDegree+12
  refine ⟨coefficient,degree,?_,by dsimp only [degree];omega,?_⟩
  · have fixed : 0<Budget.coefficient := by decide
    dsimp only [coefficient]
    omega
  · intro I input contract budget
    let S:=arithmeticScale input contract budget
    let bits:=preparationInput input contract budget
    have positive : 1≤S := by dsimp only [S,arithmeticScale];omega
    have cubic : S≤S^3 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤3)
    have one : 1≤S^3:=positive.trans cubic
    have number : I.stageCount≤Budget.coefficient*S^3 :=
      ((stage_count_bound input contract budget).trans cubic).trans (Nat.le_mul_of_pos_left _ (by decide : 0<Budget.coefficient))
    have tail : ([] : List Bool).length≤Budget.coefficient*S^3 := Nat.zero_le _
    have cost:=eBound I input contract budget (metadataBank bits I.stageCount I.toolCount budget) []
      (metadata_mass_bound input contract budget) tail (budget_field_bound input contract budget) number
    have physical:=data_bounds input contract budget
    have inputLength : bits.length+1≤S:=Budget.length_le_arithmeticScale input contract budget
    have natural : NatPacket.coefficient*(RatInput.occupied (exponentBank bits I.stageCount I.toolCount budget)+1)≤
        (NatPacket.coefficient*(dataCoefficient+1))*S^3 := by
      have inside : RatInput.occupied (exponentBank bits I.stageCount I.toolCount budget)+1≤(dataCoefficient+1)*S^3 := by
        nlinarith only [physical.1,one]
      exact (Nat.mul_le_mul_left NatPacket.coefficient inside).trans_eq (by ring)
    have cleared : (movedBank bits I.stageCount I.toolCount budget 7).length+2≤(dataCoefficient+2)*S^3 := by
      nlinarith only [physical.2.2,one]
    have scale : StageChannels.scale (stageBank bits I.stageCount I.toolCount budget) bits.length≤(dataCoefficient+1)*S^3 := by
      change RatInput.occupied (stageBank bits I.stageCount I.toolCount budget)+bits.length+1≤_
      nlinarith only [physical.2.1,inputLength,cubic]
    have channels : StageChannels.coefficient*(StageChannels.scale (stageBank bits I.stageCount I.toolCount budget) bits.length)^4≤
        (StageChannels.coefficient*(dataCoefficient+1)^4)*S^12 := by
      exact (Nat.mul_le_mul_left StageChannels.coefficient (Nat.pow_le_pow_left scale 4)).trans_eq (by ring)
    have first : Budget.coefficient*(bits.length+1)^3≤Budget.coefficient*S^3 :=
      Nat.mul_le_mul_left Budget.coefficient (Nat.pow_le_pow_left inputLength 3)
    have p3 : S^3≤S^degree:=Nat.pow_le_pow_right positive (by dsimp only [degree];omega)
    have p12 : S^12≤S^degree:=Nat.pow_le_pow_right positive (by dsimp only [degree];omega)
    have pE : S^eDegree≤S^degree:=Nat.pow_le_pow_right positive (by dsimp only [degree];omega)
    have a:=first.trans (Nat.mul_le_mul_left Budget.coefficient p3)
    have b:=cost.trans (Nat.mul_le_mul_left eCoefficient pE)
    have c:=natural.trans (Nat.mul_le_mul_left (NatPacket.coefficient*(dataCoefficient+1)) p3)
    have d:=cleared.trans (Nat.mul_le_mul_left (dataCoefficient+2) p3)
    have e:=channels.trans (Nat.mul_le_mul_left (StageChannels.coefficient*(dataCoefficient+1)^4) p12)
    change Budget.coefficient*(bits.length+1)^3+
      Global.totalCost (metadataBank bits I.stageCount I.toolCount budget) [] budget I.stageCount+
      NatPacket.coefficient*(RatInput.occupied (exponentBank bits I.stageCount I.toolCount budget)+1)+
      (movedBank bits I.stageCount I.toolCount budget 7).length+2+
      StageChannels.coefficient*(StageChannels.scale (stageBank bits I.stageCount I.toolCount budget) bits.length)^4≤coefficient*S^degree
    dsimp only [coefficient]
    nlinarith only [a,b,c,d,e]

end RootB234.PrepEntry.MainExponent
