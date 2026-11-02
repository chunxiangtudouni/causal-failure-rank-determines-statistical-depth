module
public import Common.PSTR_TM_ThresholdDepthZeroCode_167
public import Common.PSTR_TM_Overlap_132

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthZeroRun168
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMThresholdDepthZeroCode167 PSTRTMOverlap132

def contextLeft (archive previous : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks previous++false::archive

def inputRight (digits suffix : List Bool) : List Bool :=
  PSTRTMIncrement009.blocks digits++false::false::suffix

def seen (hasOne : Bool) (digits : List Bool) : Bool := hasOne||digits.any id

def frontier (archive previous : List Bool) (hasOne : Bool) (digits suffix : List Bool) : MachineState 7 :=
  state (modeLabel hasOne) (contextLeft archive previous) (inputRight digits suffix)

def final (archive previous : List Bool) (hasOne : Bool) (digits suffix : List Bool) : MachineState 7 :=
  state (haltLabel (seen hasOne digits)) (contextLeft archive (digits.reverse++previous)) (false::false::suffix)

def zeroTrace (archive previous : List Bool) (hasOne : Bool) : List Bool → List Bool → List (MachineState 7)
  | [],suffix => eofTrace hasOne (contextLeft archive previous) suffix
  | bit::later,suffix =>
    glue (unitTrace hasOne bit (contextLeft archive previous) (inputRight later suffix))
      (zeroTrace archive (bit::previous) (hasOne||bit) later suffix)

theorem zero_head (archive previous : List Bool) (hasOne : Bool) (digits suffix : List Bool) :
    (zeroTrace archive previous hasOne digits suffix).head?=some (frontier archive previous hasOne digits suffix) := by
  induction digits generalizing previous hasOne with
  | nil => rfl
  | cons bit later ih =>
    apply glue_head _ _ _ (state (modeLabel (hasOne||bit))
      (true::bit::contextLeft archive previous) (inputRight later suffix)) rfl
    · rfl
    · simpa only [frontier,contextLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_cons,List.cons_append,List.nil_append] using
        ih (bit::previous) (hasOne||bit)

theorem zero_last (archive previous : List Bool) (hasOne : Bool) (digits suffix : List Bool) :
    (zeroTrace archive previous hasOne digits suffix).getLast?=some (final archive previous hasOne digits suffix) := by
  induction digits generalizing previous hasOne with
  | nil => simp [zeroTrace,eofTrace,final,seen]
  | cons bit later ih =>
    have h := glue_last (unitTrace hasOne bit (contextLeft archive previous) (inputRight later suffix))
      (zeroTrace archive (bit::previous) (hasOne||bit) later suffix) _ (ih _ _)
    simpa only [zeroTrace,final,seen,List.any_cons,id_eq,Bool.or_assoc,List.reverse_cons,List.append_assoc,List.singleton_append] using h

theorem zero_chain (archive previous : List Bool) (hasOne : Bool) (digits suffix : List Bool) :
    (zeroTrace archive previous hasOne digits suffix).IsChain
      (fun before after => Turing.TM0.step zeroMachine before=some after) := by
  induction digits generalizing previous hasOne with
  | nil => exact eof_chain _ _ _
  | cons bit later ih =>
    apply glue_chain zeroMachine _ _ (state (modeLabel (hasOne||bit))
      (true::bit::contextLeft archive previous) (inputRight later suffix)) (unit_chain _ _ _ _) (ih _ _) rfl
    simpa only [frontier,contextLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_cons,List.cons_append,List.nil_append] using
      zero_head archive (bit::previous) (hasOne||bit) later suffix

theorem zero_length (archive previous : List Bool) (hasOne : Bool) (digits suffix : List Bool) :
    (zeroTrace archive previous hasOne digits suffix).length=2*digits.length+3 := by
  induction digits generalizing previous hasOne with
  | nil => rfl
  | cons bit later ih =>
    simp only [zeroTrace,glue_length,unitTrace,List.length_cons,List.length_nil,ih]
    omega

/-- Actual zero test, including zero-extended noncanonical words. Both
end00 cells, EVERY arbitrary right suffix cell, and all original source
and archive cells remain physically unchanged; head ends at actual EOF. -/
theorem zero_runsFrom (archive digits suffix : List Bool) :
    PSTRTMSeq005.RunsFrom zeroMachine (state 0 (false::archive) (inputRight digits suffix))
      (zeroTrace archive [] false digits suffix) (final archive [] false digits suffix) := by
  refine ⟨?_,zero_chain _ _ _ _ _,zero_last _ _ _ _ _,zero_halt _ _ _⟩
  simpa only [frontier,modeLabel,Bool.false_eq_true,↓reduceIte,contextLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_nil,List.nil_append] using
    zero_head archive [] false digits suffix

theorem zero_visitedSpace_le (archive digits suffix : List Bool) :
    visitedSpace zeroMachine (archive.length+1+2*digits.length+2+suffix.length)
      (zeroTrace archive [] false digits suffix)≤archive.length+suffix.length+6*digits.length+10 := by
  have h := PSTRTMTrace002.visitedSpace_le zeroMachine (archive.length+1+2*digits.length+2+suffix.length)
    (zeroTrace archive [] false digits suffix)
  rw [zero_length] at h
  omega

/-- The finite return-control flag is the actual numeric zero test,
including the leading zeros retained by the fixed-width countdown. -/
theorem seen_false_iff_value_zero (digits : List Bool) :
    seen false digits=false ↔ PSTRTMIncrement009.valueDigits digits=0 := by
  induction digits with
  | nil => simp [seen,PSTRTMIncrement009.valueDigits]
  | cons bit later ih =>
    cases bit with
    | false => simpa [seen,List.any_cons,PSTRTMIncrement009.valueDigits,Nat.bit] using ih
    | true => simp [seen,List.any_cons,PSTRTMIncrement009.valueDigits,Nat.bit]

theorem countdown_seen_false_iff (digits : List Bool) (hp : true∈digits) :
    seen false (PSTRTMThresholdCountdownCode164.predDigits digits)=false ↔
      PSTRTMIncrement009.valueDigits digits=1 := by
  rw [seen_false_iff_value_zero]
  have h := PSTRTMThresholdCountdownCode164.pred_value digits hp
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMThresholdDepthZeroRun168
