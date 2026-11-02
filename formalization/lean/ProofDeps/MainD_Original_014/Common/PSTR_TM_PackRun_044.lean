module
public import Common.PSTR_TM_PackLoop_043

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRun044
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMPackCode036 PSTRTMPackLoop043

def final (previous first second : List Bool) : MachineState 193 :=
  state 192 [false]
    (PSTRTMIncrement009.blocks (previous.reverse ++ pairedDigits (digitPairs first second)) ++
      [false,false,false,false,false])

private theorem column_last (previous first second : List Bool) (a b : Bool) :
    (PSTRTMPackColumns038.columnTrace a b (PSTRTMRawNat010.leftBlocks previous)
      first (PSTRTMIncrement009.blocks second)).getLast? = some (frontier (b :: a :: previous) first second) := by
  simpa [frontier_eq, PSTRTMRawNat010.leftBlocks, List.append_assoc] using
    PSTRTMPackColumns038.column_last a b (PSTRTMRawNat010.leftBlocks previous) first (PSTRTMIncrement009.blocks second)

private theorem zeroB_last (previous first : List Bool) (a : Bool) :
    (PSTRTMPackZeroB042.zeroBTrace a (PSTRTMRawNat010.leftBlocks previous) first).getLast? =
      some (frontier (false :: a :: previous) first []) := by
  simpa [frontier_eq, PSTRTMRawNat010.leftBlocks, PSTRTMIncrement009.blocks] using
    PSTRTMPackZeroB042.zeroB_last a (PSTRTMRawNat010.leftBlocks previous) first

def repairInitial (previous second : List Bool) (b : Bool) : MachineState 193 :=
  state 0 (PSTRTMRawNat010.leftBlocks (b :: false :: previous)) (true :: false :: PSTRTMIncrement009.blocks second)

private theorem zeroA_last (previous second : List Bool) (b : Bool) :
    (PSTRTMPackZeroA041.zeroATrace b (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks second)).getLast? =
      some (repairInitial previous second b) := by
  simpa [repairInitial, PSTRTMRawNat010.leftBlocks] using
    PSTRTMPackZeroA041.zeroA_last b (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks second)

private theorem repair_head (previous second : List Bool) (b : Bool) :
    (PSTRTMPackColumns038.repairTrace (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks second)).head? =
      some (repairInitial previous second b) := by
  simpa [repairInitial, List.reverse_append, PSTRTMRawNat010.leftBlocks] using
    PSTRTMPackColumns038.repair_head (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks second)

private theorem repair_last (previous second : List Bool) (b : Bool) :
    (PSTRTMPackColumns038.repairTrace (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks second)).getLast? =
      some (frontier (b :: false :: previous) [] second) := by
  simpa [frontier_eq, List.reverse_append, PSTRTMRawNat010.leftBlocks, PSTRTMIncrement009.blocks] using
    PSTRTMPackColumns038.repair_last (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks second)

theorem pack_last (previous first second : List Bool) :
    (packTrace previous first second).getLast? = some (final previous first second) := by
  cases first with
  | nil =>
    cases second with
    | nil => simpa [packTrace, final, pairedDigits, digitPairs] using PSTRTMPackFinish039.finish_last previous
    | cons b rest =>
      rw [packTrace]
      have hr := glue_last _ _ _ _ (repair_last previous rest b)
        (pack_head (b :: false :: previous) [] rest) (pack_last (b :: false :: previous) [] rest)
      have h := glue_last _ _ _ _ (zeroA_last previous rest b)
        (glue_head _ _ _ (repair_head previous rest b)) hr
      simpa [final, pairedDigits, digitPairs, List.reverse_cons, List.append_assoc] using h
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      have h := glue_last _ _ _ _ (zeroB_last previous later a)
        (pack_head (false :: a :: previous) later []) (pack_last (false :: a :: previous) later [])
      simpa [final, pairedDigits, digitPairs, List.reverse_cons, List.append_assoc] using h
    | cons b rest =>
      rw [packTrace]
      have h := glue_last _ _ _ _ (column_last previous later rest a b)
        (pack_head (b :: a :: previous) later rest) (pack_last (b :: a :: previous) later rest)
      simpa [final, pairedDigits, digitPairs, List.reverse_cons, List.append_assoc] using h
termination_by first.length + second.length
decreasing_by
  all_goals simp_wf
  omega

theorem pack_chain (previous first second : List Bool) :
    (packTrace previous first second).IsChain (fun before after => Turing.TM0.step packMachine before = some after) := by
  cases first with
  | nil =>
    cases second with
    | nil => simpa only [packTrace] using PSTRTMPackFinish039.finish_chain previous
    | cons b rest =>
      rw [packTrace]
      have hr := glue_chain _ _ _
        (PSTRTMPackColumns038.repair_chain (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks rest))
        (pack_chain (b :: false :: previous) [] rest)
        (repair_last previous rest b) (pack_head (b :: false :: previous) [] rest)
      exact glue_chain _ _ _ (PSTRTMPackZeroA041.zeroA_chain b (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks rest))
        hr (zeroA_last previous rest b) (glue_head _ _ _ (repair_head previous rest b))
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      exact glue_chain _ _ _ (PSTRTMPackZeroB042.zeroB_chain a (PSTRTMRawNat010.leftBlocks previous) later)
        (pack_chain (false :: a :: previous) later []) (zeroB_last previous later a)
        (pack_head (false :: a :: previous) later [])
    | cons b rest =>
      rw [packTrace]
      exact glue_chain _ _ _ (PSTRTMPackColumns038.column_chain a b (PSTRTMRawNat010.leftBlocks previous) later (PSTRTMIncrement009.blocks rest))
        (pack_chain (b :: a :: previous) later rest) (column_last previous later rest a b)
        (pack_head (b :: a :: previous) later rest)
termination_by first.length + second.length
decreasing_by
  all_goals simp_wf
  omega

/-- Charge every actual repeated prefix repair against the initial total
bit length. The weighted quantity previous.length+2*remaining does not grow. -/
theorem pack_length_le (previous first second : List Bool) :
    (packTrace previous first second).length ≤
      128 * (first.length + second.length + 1) * (previous.length + 2 * (first.length + second.length) + 1) := by
  cases first with
  | nil =>
    cases second with
    | nil =>
      rw [packTrace, PSTRTMPackFinish039.finish_length]
      simp only [List.length_nil]
      omega
    | cons b rest =>
      rw [packTrace]
      have h1 := glue_length_le
        (PSTRTMPackZeroA041.zeroATrace b (PSTRTMRawNat010.leftBlocks previous) (PSTRTMIncrement009.blocks rest))
        (glue (PSTRTMPackColumns038.repairTrace (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks rest))
          (packTrace (b :: false :: previous) [] rest))
      have h2 := glue_length_le
        (PSTRTMPackColumns038.repairTrace (previous.reverse ++ [false,b]) (PSTRTMIncrement009.blocks rest))
        (packTrace (b :: false :: previous) [] rest)
      have ih := pack_length_le (b :: false :: previous) [] rest
      rw [PSTRTMPackZeroA041.zeroA_length] at h1
      rw [PSTRTMPackColumns038.repair_length] at h2
      simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil] at h1 h2 ih ⊢
      nlinarith
  | cons a later =>
    cases second with
    | nil =>
      rw [packTrace]
      have h := glue_length_le (PSTRTMPackZeroB042.zeroBTrace a (PSTRTMRawNat010.leftBlocks previous) later)
        (packTrace (false :: a :: previous) later [])
      have ih := pack_length_le (false :: a :: previous) later []
      rw [PSTRTMPackZeroB042.zeroB_length] at h
      simp only [List.length_cons, List.length_nil] at h ih ⊢
      nlinarith
    | cons b rest =>
      rw [packTrace]
      have h := glue_length_le
        (PSTRTMPackColumns038.columnTrace a b (PSTRTMRawNat010.leftBlocks previous) later (PSTRTMIncrement009.blocks rest))
        (packTrace (b :: a :: previous) later rest)
      have ih := pack_length_le (b :: a :: previous) later rest
      rw [PSTRTMPackColumns038.column_length] at h
      simp only [List.length_cons] at h ih ⊢
      nlinarith
termination_by first.length + second.length
decreasing_by
  all_goals simp_wf
  omega

theorem pack_runs (first second : List Bool) :
    Runs packMachine (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second)
      (packTrace [] first second) (final [] first second) := by
  apply PSTRTMTrace002.runs_of_chain
  · exact pack_head [] first second
  · exact pack_chain [] first second
  · exact pack_last [] first second
  · exact pack_halt _ _

theorem pack_final_tape (first second : List Bool) :
    (final [] first second).Tape = Turing.Tape.mk₁ (PSTRTMBinaryAdd024.operandColumns (digitPairs first second)) := by
  have h := PSTRTMPackFinish039.finish_final_tape (pairedDigits (digitPairs first second)).reverse
  simpa [final, pairedDigits_blocks] using h

theorem pack_computes (first second : List Bool) :
    computes packMachine (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second)
      (PSTRTMBinaryAdd024.operandColumns (digitPairs first second))
      (256 * (first.length + second.length + 1)^2) (1024 * (first.length + second.length + 1)^2) := by
  have ht := pack_length_le [] first second
  simp only [List.length_nil] at ht
  refine ⟨packTrace [] first second, final [] first second, pack_runs first second, ?_, ?_, ?_⟩
  · rw [pack_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · nlinarith
  · have hs := PSTRTMTrace002.visitedSpace_le packMachine
      (PSTRTMIncrement009.blocks first ++ [false,false,true,false] ++ PSTRTMIncrement009.blocks second).length
      (packTrace [] first second)
    simp only [List.length_append, List.length_cons, List.length_nil, PSTRTMIncrement009.blocks_length] at hs ⊢
    nlinarith

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMPackRun044
