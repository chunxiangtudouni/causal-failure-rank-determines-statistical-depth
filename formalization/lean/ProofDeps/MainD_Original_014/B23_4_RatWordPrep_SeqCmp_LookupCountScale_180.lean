module

public import B23_4_RatWordPrep_SeqCmp_LookupCountActual_179
public import B23_4_RatWordPrep_SeqCmp_WordOriginalSizeBounds_162

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.Lookup.Count

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem linear_rat_sum (values : List Rat) (width a b : Nat)
    (fields : ∀ q∈values,RatInput.Encoder.fieldSize q≤width) :
    (values.map (fun q => a*RatInput.Encoder.fieldSize q+b)).sum≤values.length*(a*width+b) := by
  have terms : ∀ term∈values.map (fun q => a*RatInput.Encoder.fieldSize q+b),term≤a*width+b := by
    intro term member
    obtain ⟨q,present,rfl⟩ := List.mem_map.mp member
    exact Nat.add_le_add_right (Nat.mul_le_mul_left a (fields q present)) b
  simpa only [List.length_map,Nat.nsmul_eq_mul] using
    List.sum_le_length_nsmul (values.map (fun q => a*RatInput.Encoder.fieldSize q+b)) (a*width+b) terms

def uniformSetup (number mass : Nat) : Nat := 2*mass+2*(number+1)+14
noncomputable def uniformMass (truth : Bool) (caller : Statement C) (number mass : Nat) : Nat :=
  mass+pushCap truth caller*uniformSetup number mass
noncomputable def uniformPhase (truth : Bool) (caller : Statement C) (number width mass : Nat) : Nat :=
  uniformSetup number mass+256*(number+1)*(uniformMass truth caller number mass+1)+number*(3*width+14)
def uniformSelected (number width : Nat) : Nat := 6*width+28+2*number*(3*width+16)+4
noncomputable def uniformWork (truth : Bool) (caller : Statement C) (number width mass : Nat) : Nat :=
  2+uniformPhase truth caller number width (mass+1)+
    uniformPhase truth caller number width (uniformMass truth caller number (mass+1))+
    uniformSelected number width

theorem uniformMass_mono (truth : Bool) (caller : Statement C) (number : Nat) {a b : Nat} (bound : a≤b) :
    uniformMass truth caller number a≤uniformMass truth caller number b := by
  unfold uniformMass uniformSetup
  nlinarith

theorem uniformPhase_mono (truth : Bool) (caller : Statement C) (number width : Nat) {a b : Nat} (bound : a≤b) :
    uniformPhase truth caller number width a≤uniformPhase truth caller number width b := by
  have mass := uniformMass_mono truth caller number bound
  unfold uniformPhase uniformSetup
  nlinarith

theorem phaseMass_upper (truth : Bool) (caller : Statement C) (values : List Rat) (number mass : Nat)
    (count : values.length≤number) :
    phaseMass truth caller values.length mass≤uniformMass truth caller number mass := by
  have width := (WordFinish.Resources.rawPayload_le_number values.length).trans (Nat.add_le_add_right count 1)
  unfold phaseMass setupWork uniformMass uniformSetup
  nlinarith

theorem uniformWork_mono (truth : Bool) (caller : Statement C) (number width : Nat) {a b : Nat} (bound : a≤b) :
    uniformWork truth caller number width a≤uniformWork truth caller number width b := by
  have first := uniformPhase_mono truth caller number width (Nat.add_le_add_right bound 1)
  have mass := uniformMass_mono truth caller number (Nat.add_le_add_right bound 1)
  have second := uniformPhase_mono truth caller number width mass
  unfold uniformWork
  omega

theorem phaseWork_upper (truth : Bool) (caller : Statement C) (values : List Rat) (number width mass : Nat)
    (count : values.length≤number) (fields : ∀ q∈values,RatInput.Encoder.fieldSize q≤width) :
    phaseWork truth caller values mass≤uniformPhase truth caller number width mass := by
  have raw := (WordFinish.Resources.rawPayload_le_number values.length).trans (Nat.add_le_add_right count 1)
  have setup : setupWork mass values.length≤uniformSetup number mass := by unfold setupWork uniformSetup; omega
  have massBound := phaseMass_upper truth caller values number mass count
  have moves : moveWork values≤number*(3*width+14) :=
    (linear_rat_sum values width 3 14 fields).trans (Nat.mul_le_mul_right _ count)
  have loop : skipWork values (phaseMass truth caller values.length mass)≤
      256*(number+1)*(uniformMass truth caller number mass+1)+number*(3*width+14) :=
    Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_left 256 (Nat.add_le_add_right count 1))
      (Nat.add_le_add_right massBound 1)) moves
  exact (Nat.add_le_add setup loop).trans_eq (by unfold uniformPhase; ring)

theorem selectedWork_upper (earlier front : List Rat) (x : Rat) (number width : Nat)
    (earlierCount : earlier.length≤number) (frontCount : front.length≤number)
    (fields : ∀ q∈earlier++front,RatInput.Encoder.fieldSize q≤width)
    (field : RatInput.Encoder.fieldSize x≤width) :
    selectedWork (earlier++front) x≤uniformSelected number width := by
  have reversedFields : ∀ q∈(earlier++front).reverse,RatInput.Encoder.fieldSize q≤width := by
    intro q member
    exact fields q (List.mem_reverse.mp member)
  have sum := linear_rat_sum (earlier++front).reverse width 3 16 reversedFields
  have count : (earlier++front).reverse.length≤2*number := by
    simp only [List.length_reverse,List.length_append]
    omega
  have paid := sum.trans (Nat.mul_le_mul_right _ count)
  unfold selectedWork restoreWork uniformSelected
  omega

theorem actualWork_upper (truth : Bool) (caller : Statement C) (firstRow front : List Rat) (x : Rat)
    (number width mass : Nat) (firstCount : firstRow.length≤number) (frontCount : front.length≤number)
    (firstFields : ∀ q∈firstRow,RatInput.Encoder.fieldSize q≤width)
    (frontFields : ∀ q∈front,RatInput.Encoder.fieldSize q≤width)
    (field : RatInput.Encoder.fieldSize x≤width) :
    actualWork truth caller firstRow front x mass≤uniformWork truth caller number width mass := by
  cases truth with
  | false =>
    have phase := phaseWork_upper false caller front number width (mass+1) frontCount frontFields
    have selected := selectedWork_upper [] front x number width (by simp) frontCount
      (by simpa only [List.nil_append] using frontFields) field
    have enlarged : mass+1≤uniformMass false caller number (mass+1) := by unfold uniformMass; omega
    have monotone := uniformPhase_mono false caller number width enlarged
    simp only [actualWork,Bool.false_eq_true,ite_false,finishWork,uniformWork]
    omega
  | true =>
    have first := phaseWork_upper true caller firstRow number width (mass+1) firstCount firstFields
    have frontPart := phaseWork_upper true caller front number width
      (phaseMass true caller firstRow.length (mass+1)) frontCount frontFields
    have massBound := phaseMass_upper true caller firstRow number (mass+1) firstCount
    have enlarged := uniformPhase_mono true caller number width massBound
    have selected := selectedWork_upper firstRow front x number width firstCount frontCount
      (by intro q member; rcases List.mem_append.mp member with left | right
          · exact firstFields q left
          · exact frontFields q right) field
    simp only [actualWork,ite_true,finishWork,uniformWork]
    omega

end B23_4_RatWordPrep.Lookup.Count
