module
public import Common.PSTR_TM_PackFrameRun_149

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameCost150
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMOverlap132 PSTRTMPackFrameRun149

/-- The physical potential previous.length+2*remaining bounds all actual
shuttles, including the new right-padding scan of the remaining B field.
Every recursive call below concerns the SAME fixed146 machine and trace. -/
theorem pack_length_le (archive previous first second : List Bool) :
    (packTrace archive previous first second).length≤
      128*(first.length+second.length+1)*(previous.length+2*(first.length+second.length)+1) := by
  cases first with
  | nil =>
    cases second with
    | nil =>
      rw [packTrace,PSTRTMPackFinishFrame143.finish_length]
      simp only [List.length_nil]
      omega
    | cons b rest =>
      rw [packTrace]
      have h1 := glue_length_le
        (PSTRTMPackZeroA041.zeroATrace b (contextLeft archive previous) (PSTRTMIncrement009.blocks rest))
        (glue (PSTRTMPackRepairFrame147.repairTrace (contextLeft archive (b::false::previous)) rest)
          (packTrace archive (b::false::previous) [] rest))
      have h2 := glue_length_le
        (PSTRTMPackRepairFrame147.repairTrace (contextLeft archive (b::false::previous)) rest)
        (packTrace archive (b::false::previous) [] rest)
      have ih := pack_length_le archive (b::false::previous) [] rest
      rw [PSTRTMPackZeroA041.zeroA_length] at h1
      rw [PSTRTMPackRepairFrame147.repair_length] at h2
      simp only [List.length_cons,List.length_nil] at h1 h2 ih ⊢
      nlinarith
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      have h := glue_length_le (PSTRTMPackZeroB042.zeroBTrace a (contextLeft archive previous) later)
        (packTrace archive (false::a::previous) later [])
      have ih := pack_length_le archive (false::a::previous) later []
      rw [PSTRTMPackZeroB042.zeroB_length] at h
      simp only [List.length_cons,List.length_nil] at h ih ⊢
      nlinarith
    | cons b rest =>
      rw [packTrace]
      have h := glue_length_le
        (PSTRTMPackColumns038.columnTrace a b (contextLeft archive previous) later (PSTRTMIncrement009.blocks rest))
        (packTrace archive (b::a::previous) later rest)
      have ih := pack_length_le archive (b::a::previous) later rest
      rw [PSTRTMPackColumns038.column_length] at h
      simp only [List.length_cons] at h ih ⊢
      nlinarith
termination_by first.length+second.length
decreasing_by
  all_goals simp_wf
  omega

theorem initial_pack_length_le (archive first second : List Bool) :
    (packTrace archive [] first second).length≤256*(first.length+second.length+1)^2 := by
  have h := pack_length_le archive [] first second
  simp only [List.length_nil] at h
  nlinarith

private theorem one_add_le_square (width : Nat) : width+1≤(width+1)^2 := by
  have h := Nat.mul_le_mul_left (width+1) (by omega : 1≤width+1)
  simpa only [Nat.mul_one,pow_two] using h

/-- Original visitedSpace of the same genuine trace. The charged initial
cells include the actual archived data, false guard, both source fields
and real0010 separator. There is no spacer/cost/length oracle in the code. -/
theorem pack_visitedSpace_le (archive first second : List Bool) :
    visitedSpace PSTRTMPackFrameCode146.packMachine
      (archive.length+1+(2*first.length+4+2*second.length))
      (packTrace archive [] first second)≤archive.length+1024*(first.length+second.length+1)^2 := by
  have ht := initial_pack_length_le archive first second
  have hs := PSTRTMTrace002.visitedSpace_le PSTRTMPackFrameCode146.packMachine
    (archive.length+1+(2*first.length+4+2*second.length)) (packTrace archive [] first second)
  have hq := one_add_le_square (first.length+second.length)
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameCost150
