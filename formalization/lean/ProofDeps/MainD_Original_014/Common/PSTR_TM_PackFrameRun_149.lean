module
public import Common.PSTR_TM_PackFrameUnits_148
public import Common.PSTR_TM_PackLoop_043

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameRun149
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMOverlap132

def contextLeft (archive previous : List Bool) : List Bool :=
  PSTRTMRawNat010.leftBlocks previous++false::archive

def frontier (archive previous first second : List Bool) : MachineState 193 :=
  state 0 (contextLeft archive previous)
    (PSTRTMIncrement009.blocks first++[false,false,true,false]++PSTRTMIncrement009.blocks second)

def final (archive previous first second : List Bool) : MachineState 193 :=
  state 192 (false::archive)
    (PSTRTMIncrement009.blocks (previous.reverse++PSTRTMPackLoop043.pairedDigits (digitPairs first second))++
      [false,false,false,false,false])

/-- Ghost structural recursion describes actual146 execution only. All
operand endpoints are read from real flags; there is no length/fuel input.
The A-empty case calls the actual RIGHT insertion147, preserving archive. -/
def packTrace (archive previous first second : List Bool) : List (MachineState 193) :=
  match first,second with
  | [],[] => PSTRTMPackFinishFrame143.finishTrace archive previous
  | a::later,b::rest => glue
      (PSTRTMPackColumns038.columnTrace a b (contextLeft archive previous) later (PSTRTMIncrement009.blocks rest))
      (packTrace archive (b::a::previous) later rest)
  | a::later,[] => glue
      (PSTRTMPackZeroB042.zeroBTrace a (contextLeft archive previous) later)
      (packTrace archive (false::a::previous) later [])
  | [],b::rest => glue
      (PSTRTMPackZeroA041.zeroATrace b (contextLeft archive previous) (PSTRTMIncrement009.blocks rest))
      (glue (PSTRTMPackRepairFrame147.repairTrace (contextLeft archive (b::false::previous)) rest)
        (packTrace archive (b::false::previous) [] rest))
termination_by first.length+second.length
decreasing_by
  all_goals simp_wf
  omega

private theorem glue_head_of_two (first second : List (MachineState 193)) (initial : MachineState 193)
    (hl : 2≤first.length) (hh : first.head?=some initial) : (glue first second).head?=some initial := by
  cases first with
  | nil => simp at hl
  | cons current rest =>
    cases rest with
    | nil => simp at hl
    | cons next later =>
      simpa only [glue,List.dropLast_cons_cons,List.cons_append,List.head?_cons] using hh

theorem pack_head (archive previous first second : List Bool) :
    (packTrace archive previous first second).head?=some (frontier archive previous first second) := by
  cases first with
  | nil =>
    cases second with
    | nil =>
      simpa [packTrace,frontier,contextLeft,PSTRTMIncrement009.blocks] using
        PSTRTMPackFinishFrame143.finish_head archive previous
    | cons b rest =>
      rw [packTrace]
      have hl : 2≤(PSTRTMPackZeroA041.zeroATrace b (contextLeft archive previous) (PSTRTMIncrement009.blocks rest)).length := by
        rw [PSTRTMPackZeroA041.zeroA_length]; omega
      simpa [frontier,PSTRTMIncrement009.blocks] using
        glue_head_of_two _
          (glue (PSTRTMPackRepairFrame147.repairTrace (contextLeft archive (b::false::previous)) rest)
            (packTrace archive (b::false::previous) [] rest))
          _ hl (PSTRTMPackZeroA041.zeroA_head _ _ _)
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      have hl : 2≤(PSTRTMPackZeroB042.zeroBTrace a (contextLeft archive previous) later).length := by
        rw [PSTRTMPackZeroB042.zeroB_length]; omega
      have hh := glue_head_of_two _ (packTrace archive (false::a::previous) later []) _ hl
        (PSTRTMPackZeroB042.zeroB_head _ _ _)
      have hz : a::true::(PSTRTMIncrement009.blocks later++[false,false,true,false,false,false])=
          (a::true::(PSTRTMIncrement009.blocks later++[false,false,true,false]))++List.replicate 2 false := by
        simp [List.append_assoc]
      rw [hz,PSTRTMPackLoop043.state_false_suffix] at hh
      simpa [frontier,PSTRTMIncrement009.blocks] using hh
    | cons b rest =>
      rw [packTrace]
      have hl : 2≤(PSTRTMPackColumns038.columnTrace a b (contextLeft archive previous) later (PSTRTMIncrement009.blocks rest)).length := by
        rw [PSTRTMPackColumns038.column_length]; omega
      simpa [frontier,PSTRTMIncrement009.blocks,List.append_assoc] using
        glue_head_of_two _ (packTrace archive (b::a::previous) later rest) _ hl
          (PSTRTMPackColumns038.column_head _ _ _ _ _)

private theorem column_last (archive previous first second : List Bool) (a b : Bool) :
    (PSTRTMPackColumns038.columnTrace a b (contextLeft archive previous) first (PSTRTMIncrement009.blocks second)).getLast?=
      some (frontier archive (b::a::previous) first second) := by
  simpa [frontier,contextLeft,PSTRTMRawNat010.leftBlocks,List.append_assoc] using
    PSTRTMPackColumns038.column_last a b (contextLeft archive previous) first (PSTRTMIncrement009.blocks second)

private theorem zeroB_last (archive previous first : List Bool) (a : Bool) :
    (PSTRTMPackZeroB042.zeroBTrace a (contextLeft archive previous) first).getLast?=
      some (frontier archive (false::a::previous) first []) := by
  simpa [frontier,contextLeft,PSTRTMRawNat010.leftBlocks,PSTRTMIncrement009.blocks,List.append_assoc] using
    PSTRTMPackZeroB042.zeroB_last a (contextLeft archive previous) first

private theorem zeroA_last (archive previous second : List Bool) (b : Bool) :
    (PSTRTMPackZeroA041.zeroATrace b (contextLeft archive previous) (PSTRTMIncrement009.blocks second)).getLast?=
      some (PSTRTMPackRepairFrame147.repairInitial (contextLeft archive (b::false::previous)) second) := by
  simpa [PSTRTMPackRepairFrame147.repairInitial,contextLeft,PSTRTMRawNat010.leftBlocks] using
    PSTRTMPackZeroA041.zeroA_last b (contextLeft archive previous) (PSTRTMIncrement009.blocks second)

private theorem repair_last (archive previous second : List Bool) :
    (PSTRTMPackRepairFrame147.repairTrace (contextLeft archive previous) second).getLast?=
      some (frontier archive previous [] second) := by
  simpa [PSTRTMPackRepairFrame147.repairFinal,frontier,PSTRTMIncrement009.blocks] using
    PSTRTMPackRepairFrame147.repair_last (contextLeft archive previous) second

theorem pack_last (archive previous first second : List Bool) :
    (packTrace archive previous first second).getLast?=some (final archive previous first second) := by
  cases first with
  | nil =>
    cases second with
    | nil =>
      simpa [packTrace,final,PSTRTMPackLoop043.pairedDigits,digitPairs] using
        PSTRTMPackFinishFrame143.finish_last archive previous
    | cons b rest =>
      rw [packTrace]
      have hi := glue_last (PSTRTMPackRepairFrame147.repairTrace (contextLeft archive (b::false::previous)) rest)
        (packTrace archive (b::false::previous) [] rest) _ (pack_last archive (b::false::previous) [] rest)
      have h := glue_last
        (PSTRTMPackZeroA041.zeroATrace b (contextLeft archive previous) (PSTRTMIncrement009.blocks rest)) _ _ hi
      simpa [final,PSTRTMPackLoop043.pairedDigits,digitPairs,List.reverse_cons,List.append_assoc] using h
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      have h := glue_last (PSTRTMPackZeroB042.zeroBTrace a (contextLeft archive previous) later)
        (packTrace archive (false::a::previous) later []) _ (pack_last archive (false::a::previous) later [])
      simpa [final,PSTRTMPackLoop043.pairedDigits,digitPairs,List.reverse_cons,List.append_assoc] using h
    | cons b rest =>
      rw [packTrace]
      have h := glue_last
        (PSTRTMPackColumns038.columnTrace a b (contextLeft archive previous) later (PSTRTMIncrement009.blocks rest))
        (packTrace archive (b::a::previous) later rest) _ (pack_last archive (b::a::previous) later rest)
      simpa [final,PSTRTMPackLoop043.pairedDigits,digitPairs,List.reverse_cons,List.append_assoc] using h
termination_by first.length+second.length
decreasing_by
  all_goals simp_wf
  omega

theorem pack_chain (archive previous first second : List Bool) :
    (packTrace archive previous first second).IsChain
      (fun before after => Turing.TM0.step PSTRTMPackFrameCode146.packMachine before=some after) := by
  cases first with
  | nil =>
    cases second with
    | nil => simpa only [packTrace] using PSTRTMPackFrameUnits148.finish_chain archive previous
    | cons b rest =>
      rw [packTrace]
      have hi := glue_chain PSTRTMPackFrameCode146.packMachine _ _ _
        (PSTRTMPackRepairFrame147.repair_chain (contextLeft archive (b::false::previous)) rest)
        (pack_chain archive (b::false::previous) [] rest)
        (repair_last archive (b::false::previous) rest) (pack_head archive (b::false::previous) [] rest)
      have hl : 2≤(PSTRTMPackRepairFrame147.repairTrace (contextLeft archive (b::false::previous)) rest).length := by
        rw [PSTRTMPackRepairFrame147.repair_length]; omega
      exact glue_chain PSTRTMPackFrameCode146.packMachine _ _ _
        (PSTRTMPackFrameUnits148.zeroA_chain _ _ _) hi (zeroA_last archive previous rest b)
        (glue_head_of_two _ (packTrace archive (b::false::previous) [] rest) _ hl
          (PSTRTMPackRepairFrame147.repair_head _ _))
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      exact glue_chain PSTRTMPackFrameCode146.packMachine _ _ _
        (PSTRTMPackFrameUnits148.zeroB_chain _ _ _) (pack_chain archive (false::a::previous) later [])
        (zeroB_last archive previous later a) (pack_head archive (false::a::previous) later [])
    | cons b rest =>
      rw [packTrace]
      exact glue_chain PSTRTMPackFrameCode146.packMachine _ _ _
        (PSTRTMPackFrameUnits148.column_chain _ _ _ _ _) (pack_chain archive (b::a::previous) later rest)
        (column_last archive previous later rest a b) (pack_head archive (b::a::previous) later rest)
termination_by first.length+second.length
decreasing_by
  all_goals simp_wf
  omega

/-- Genuine full new194-label archive-preserving packer. The same code
handles all zero/empty/unequal-width cases, including actual right padding.
The right tape is blank beyond the two source fields. -/
theorem pack_runsFrom (archive first second : List Bool) :
    PSTRTMSeq005.RunsFrom PSTRTMPackFrameCode146.packMachine
      (state 0 (false::archive)
        (PSTRTMIncrement009.blocks first++[false,false,true,false]++PSTRTMIncrement009.blocks second))
      (packTrace archive [] first second) (final archive [] first second) := by
  refine ⟨?_,pack_chain _ _ _ _,pack_last _ _ _ _,PSTRTMPackFrameCode146.pack_halt _ _⟩
  simpa only [frontier,contextLeft,PSTRTMRawNat010.leftBlocks,List.flatMap_nil,List.nil_append] using
    pack_head archive [] first second

theorem pack_final_tape (archive first second : List Bool) :
    (final archive [] first second).Tape=Turing.Tape.mk₂ (false::archive)
      (PSTRTMBinaryAdd024.operandColumns (digitPairs first second)) := by
  have h := PSTRTMPackFinishFrame143.finish_final_tape archive
    (PSTRTMPackLoop043.pairedDigits (digitPairs first second)).reverse
  simpa only [final,List.reverse_nil,List.nil_append,List.reverse_reverse,PSTRTMPackLoop043.pairedDigits_blocks] using h

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackFrameRun149
