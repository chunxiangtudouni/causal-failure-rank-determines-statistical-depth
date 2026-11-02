module

public import RootB234_PrepEntry_StageChannelsRun_061

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep PA17TMRatArithmeticParse002

variable {I : Instance}

theorem fields_count (values : List Rat) : values.length≤(Channels.fields values).length := by
  induction values with
  | nil => rfl
  | cons x later ih =>
    have field : 1≤(encodeDatum (.rational x)).length := by rw [datum_length]; omega
    simp only [Channels.fields,List.flatMap_cons,List.length_append,List.length_cons] at ih ⊢
    omega

theorem field_member (values : List Rat) (x : Rat) (member : x∈values) :
    (encodeDatum (.rational x)).length≤(Channels.fields values).length := by
  induction values with
  | nil => cases member
  | cons first later ih =>
    rcases List.mem_cons.mp member with rfl|member
    · simp only [Channels.fields,List.flatMap_cons,List.length_append]; omega
    · have part:=ih member
      simp only [Channels.fields,List.flatMap_cons,List.length_append] at part ⊢
      omega

theorem datum_time (x : Rat) (length : Nat) (encoded : (encodeDatum (.rational x)).length≤length) :
    RatInput.Encoder.fieldSize x≤length ∧ RawGetter.time x≤64*(length+1)^2 := by
  have widths : (numeratorDigits x).length+(denominatorDigits x).length≤length := by
    rw [datum_length] at encoded
    omega
  have squared : (numeratorDigits x).length^2+(denominatorDigits x).length^2≤length^2 := by
    have sum:=Nat.pow_le_pow_left widths 2
    nlinarith only [sum,Nat.zero_le ((numeratorDigits x).length*(denominatorDigits x).length)]
  refine ⟨widths,?_⟩
  dsimp only [RawGetter.time]
  nlinarith only [widths,squared,Nat.zero_le (length^2)]

theorem vector_credit (values : List Rat) (length : Nat) (encoded : (Channels.fields values).length≤length) :
    values.length≤length ∧ Bounds.credits values≤4096*(length+1)^3 := by
  have count:=(fields_count values).trans encoded
  have termwise : ∀ value∈values.map Bounds.credit,value≤4096*(length+1)^2 := by
    intro value member
    obtain ⟨x,present,rfl⟩:=List.mem_map.mp member
    have data:=(field_member values x present).trans encoded
    obtain ⟨width,time⟩:=datum_time x length data
    have linear : length+1≤(length+1)^2 := by nlinarith only [Nat.zero_le length]
    dsimp only [Bounds.credit]
    omega
  have sum : Bounds.credits values≤values.length*(4096*(length+1)^2) := by
    simpa only [Bounds.credits,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (values.map Bounds.credit) (4096*(length+1)^2) termwise
  refine ⟨count,?_⟩
  calc
    Bounds.credits values≤(length+1)*(4096*(length+1)^2) :=
      sum.trans (Nat.mul_le_mul_right _ (by omega : values.length≤length+1))
    _=_ := by ring

theorem channel_blocks (input : StatisticalInput I) (contract : Contract I) (budget : Rat) (positive : 0<I.stageCount) :
    (Channels.fields (values (input.experiment ⟨0,positive⟩) false)).length+
      (Channels.fields (values (input.experiment ⟨0,positive⟩) true)).length≤(preparationInput input contract budget).length := by
  have sub : (NJ.afterTools input contract budget).length≤(preparationInput input contract budget).length := by
    change (((PSTRTMWordPreparationFront214.preparationData input contract budget).drop 2).flatMap encodeDatum++[true]).length≤
      (encode (PSTRTMWordPreparationFront214.preparationData input contract budget)).length
    have split:=List.take_append_drop 2 (PSTRTMWordPreparationFront214.preparationData input contract budget)
    have encoded:=congrArg (fun data : List Datum => data.flatMap encodeDatum) split
    have lengths:=congrArg List.length encoded
    simp only [List.flatMap_append,List.length_append] at lengths
    simp only [encode,List.length_append]
    omega
  rw [FirstRaw.afterTools_exact,FirstRaw.wireSuffix_positive input contract budget positive] at sub
  simp only [FirstRaw.channelValues,values,Channels.fields,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.flatMap_append,List.length_append] at sub ⊢
  omega

theorem limit_envelope (values : List Rat) (bound scale : Nat) (positive : 1≤scale)
    (count : values.length+1≤scale) (room : bound+Bounds.credits values≤2097152*scale^3)
    (credit : Bounds.credits values≤4096*scale^3) :
    Bounds.limit values bound≤17179869184*scale^4 := by
  have linear : scale≤scale^4 := by simpa only [pow_one] using Nat.pow_le_pow_right positive (by decide : 1≤4)
  have cubic : scale^3≤scale^4 := Nat.pow_le_pow_right positive (by decide : 3≤4)
  calc
    Bounds.limit values bound≤scale*(4096*(2097152*scale^3)+256)+4096*scale^3 :=
      Nat.add_le_add (Nat.mul_le_mul count (Nat.add_le_add_right (Nat.mul_le_mul_left 4096 room) 256)) credit
    _=8589934592*scale^4+256*scale+4096*scale^3 := by ring
    _≤_ := by nlinarith only [linear,cubic]

/-- A deliberately conservative fixed degree. A is occupied original
background plus the genuine original input length plus one. It is never
a runtime counter, scanner fuel or caller premise. -/
theorem totalTime_le (background : RatInput.Stack → List Bool) (input : StatisticalInput I) (contract : Contract I) (budget : Rat) :
    totalTime background input contract budget≤137438953472*(StageFront.scale background (preparationInput input contract budget).length)^4 := by
  let length:=(preparationInput input contract budget).length
  let scale:=StageFront.scale background length
  have base : 1≤scale := by dsimp [scale,StageFront.scale]; omega
  have linear : scale≤scale^3 := by simpa only [pow_one] using Nat.pow_le_pow_right base (by decide : 1≤3)
  have square : scale^2≤scale^3 := Nat.pow_le_pow_right base (by decide : 2≤3)
  have cubic : scale^3≤scale^4 := Nat.pow_le_pow_right base (by decide : 3≤4)
  have unit : 1≤scale^3 := Nat.pow_le_pow_left base 3
  have unit4 : 1≤scale^4 := Nat.pow_le_pow_left base 4
  have inputScale : length+1≤scale := by dsimp [scale,StageFront.scale]; omega
  by_cases positive : 0<I.stageCount
  · let experiment:=input.experiment ⟨0,positive⟩
    let cap:=frontCap background input contract budget
    let width:=(PSTRTMNatValue017.rawPayload experiment.alphabetSize).length
    have blocks:=channel_blocks input contract budget positive
    change (Channels.fields (values experiment false)).length+
      (Channels.fields (values experiment true)).length≤length at blocks
    have leftBlock : (Channels.fields (values experiment false)).length≤length := by omega
    have rightBlock : (Channels.fields (values experiment true)).length≤length := by omega
    obtain ⟨leftCount,leftCredit⟩:=vector_credit (values experiment false) length leftBlock
    obtain ⟨rightCount,rightCredit⟩:=vector_credit (values experiment true) length rightBlock
    have leftC : Bounds.credits (values experiment false)≤4096*scale^3 :=
      leftCredit.trans (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left inputScale 3))
    have rightC : Bounds.credits (values experiment true)≤4096*scale^3 :=
      rightCredit.trans (Nat.mul_le_mul_left 4096 (Nat.pow_le_pow_left inputScale 3))
    have widthInput : width≤length := by
      have same:=FirstRaw.lastNatural_width_le input contract budget
      rw [FirstRaw.lastNatural_positive input contract positive] at same
      exact same
    have widthC : width≤scale^3 := widthInput.trans ((by omega : length≤scale).trans linear)
    have wholeRoom : buildSpace experiment.alphabetSize
        (buildSpace experiment.alphabetSize cap+Bounds.credits (values experiment false))+
          Bounds.credits (values experiment true)≤2097152*scale^3 := by
      change 1048576*scale^2+2*width+4+Bounds.credits (values experiment false)+2*width+4+
        Bounds.credits (values experiment true)≤2097152*scale^3
      nlinarith only [leftC,rightC,widthC,square,unit]
    have leftRoom : buildSpace experiment.alphabetSize cap+Bounds.credits (values experiment false)≤2097152*scale^3 := by
      dsimp only [buildSpace] at wholeRoom ⊢
      omega
    have leftTime:=limit_envelope (values experiment false) (buildSpace experiment.alphabetSize cap) scale base
      (by omega) leftRoom leftC
    have rightTime:=limit_envelope (values experiment true)
      (buildSpace experiment.alphabetSize (buildSpace experiment.alphabetSize cap+Bounds.credits (values experiment false))) scale base
      (by omega) wholeRoom rightC
    have capC : cap≤2097152*scale^3 := by change 1048576*scale^2≤_; omega
    have afterLeftC : buildSpace experiment.alphabetSize cap+Bounds.credits (values experiment false)≤2097152*scale^3 := leftRoom
    have firstBuild : buildLimit experiment.alphabetSize cap≤8388608*scale^4 := by
      change 2*cap+2*width+14≤_
      nlinarith only [capC,widthC,unit,cubic]
    have secondBuild : buildLimit experiment.alphabetSize
        (buildSpace experiment.alphabetSize cap+Bounds.credits (values experiment false))≤8388608*scale^4 := by
      change 2*(buildSpace experiment.alphabetSize cap+Bounds.credits (values experiment false))+2*width+14≤_
      nlinarith only [afterLeftC,widthC,unit,cubic]
    simp only [totalTime,dite_eq_left positive]
    change cap+2+_+_+_+_≤137438953472*scale^4
    nlinarith only [capC,cubic,unit4,firstBuild,secondBuild,leftTime,rightTime]
  · simp only [totalTime,dite_eq_right positive]
    change 1048576*scale^2+2≤137438953472*scale^4
    nlinarith only [square,cubic,unit4]

end RootB234.PrepEntry.StageChannels
