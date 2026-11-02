module
public import PaperProofs.Common.PSTR_TM_CompareErase_058
public import PaperProofs.Common.PSTR_TM_PackLoop_043
import Mathlib.Tactic.FinCases

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareRun059
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRTMCompareFinishCode057

theorem kernel_command (q next : Fin 21) (symbol : Bool) (statement : Turing.TM0.Stmt Bool)
    (old : PSTRTMCompareCode054.compareMachine q symbol = some (next, statement)) :
    resultMachine (embedKernel q) symbol = some (embedKernel next, statement) := by
  have hq : q.val < 18 := by
    by_contra hn
    simp [PSTRTMCompareCode054.compareMachine, show ¬q.val < 3 by omega,
      show ¬q.val < 9 by omega, show ¬q.val < 15 by omega, hn] at old
  simp [resultMachine, embedKernel, hq, old]

theorem kernel_step (before after : MachineState 20)
    (old : Turing.TM0.step PSTRTMCompareCode054.compareMachine before = some after) :
    Turing.TM0.step resultMachine (liftKernel before) = some (liftKernel after) := by
  cases before with
  | mk q tape =>
    unfold Turing.TM0.step at old
    cases hc : PSTRTMCompareCode054.compareMachine q tape.head with
    | none => simp [hc] at old
    | some command =>
      obtain ⟨next, statement⟩ := command
      simp only [hc, Option.map_some, Option.some.injEq] at old
      subst after
      have hm := kernel_command q next tape.head statement hc
      simp only [Turing.TM0.step, liftKernel, hm, Option.map_some]

theorem kernel_chain (trace : List (MachineState 20))
    (old : trace.IsChain (fun a b => Turing.TM0.step PSTRTMCompareCode054.compareMachine a = some b)) :
    (trace.map liftKernel).IsChain (fun a b => Turing.TM0.step resultMachine a = some b) := by
  apply (List.isChain_map _).mpr
  exact old.imp kernel_step

private theorem leftColumns_append (xs ys : List (Bool × Bool)) :
    PSTRTMCompareCode054.leftColumns (xs ++ ys) =
      PSTRTMCompareCode054.leftColumns xs ++ PSTRTMCompareCode054.leftColumns ys := by
  simp only [PSTRTMCompareCode054.leftColumns, List.flatMap_append]

private theorem leftBlocks_append (xs ys : List Bool) :
    PSTRTMRawNat010.leftBlocks (xs ++ ys) = PSTRTMRawNat010.leftBlocks xs ++ PSTRTMRawNat010.leftBlocks ys := by
  simp only [PSTRTMRawNat010.leftBlocks, List.flatMap_append]

theorem leftColumns_reverse (pairs : List (Bool × Bool)) :
    PSTRTMCompareCode054.leftColumns pairs.reverse =
      PSTRTMRawNat010.leftBlocks (PSTRTMPackLoop043.pairedDigits pairs).reverse := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    rw [List.reverse_cons, leftColumns_append, ih]
    change _ = PSTRTMRawNat010.leftBlocks (a :: b :: PSTRTMPackLoop043.pairedDigits later).reverse
    simp only [List.reverse_cons, leftBlocks_append]
    simp [PSTRTMCompareCode054.leftColumns, PSTRTMRawNat010.leftBlocks, List.append_assoc]

theorem pairedDigits_length (pairs : List (Bool × Bool)) :
    (PSTRTMPackLoop043.pairedDigits pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change (a :: b :: PSTRTMPackLoop043.pairedDigits later).length = _
    simp only [List.length_cons, ih]
    omega

theorem kernel_erase_transfer (relation : Fin 3) (previous : List Bool) (cleared : Nat) :
    Turing.TM0.step resultMachine
      (liftKernel (PSTRTMCompareCode054.state (PSTRTMCompareCode054.haltLabel relation)
        (PSTRTMRawNat010.leftBlocks previous) (List.replicate cleared false))) =
      some (PSTRTMCompareErase058.eraseInitial relation previous cleared) := by
  fin_cases relation <;> cases previous <;>
    simp [Turing.TM0.step, resultMachine, liftKernel, embedKernel, PSTRTMCompareCode054.state,
      PSTRTMCompareCode054.haltLabel, PSTRTMCompareErase058.eraseInitial,
      PSTRTMRawNat010.leftBlocks, state, eraseFlag, Turing.Tape.mk₂, List.replicate_succ]

/-- The trace contains every retained kernel step, the REAL left transfer,
every flag/data erase, all three output writes, and the actual rewind. -/
def resultTrace (pairs : List (Bool × Bool)) : List (MachineState 52) :=
  (PSTRTMCompareTrace055.compareTrace 0 [] [] pairs []).map liftKernel ++
    PSTRTMCompareErase058.eraseTrace (PSTRTMCompareCode054.resultRelation 0 pairs)
      (PSTRTMPackLoop043.pairedDigits pairs).reverse 2

def resultFinal (pairs : List (Bool × Bool)) : MachineState 52 :=
  state 52 [false] (outputWord (PSTRTMCompareCode054.resultRelation 0 pairs))

theorem result_head (pairs : List (Bool × Bool)) :
    (resultTrace pairs).head? = some (state 0 [] (PSTRTMBinaryAdd024.operandColumns pairs)) := by
  simp only [resultTrace, List.head?_append, List.head?_map, PSTRTMCompareTrace055.compare_head,
    Option.map_some, Option.some_or, PSTRTMCompareCode054.leftColumns, List.flatMap_nil,
    List.nil_append]
  change some (state 0 [] (PSTRTMBinaryAdd024.operandColumns pairs ++ [false,false])) = _
  have hb := PSTRTMPackFinish039.blank_false_suffix (PSTRTMBinaryAdd024.operandColumns pairs) 2
  change Turing.ListBlank.mk (PSTRTMBinaryAdd024.operandColumns pairs ++ [false,false]) = _ at hb
  simp only [state, Turing.Tape.mk₂]
  rw [hb]

theorem result_last (pairs : List (Bool × Bool)) :
    (resultTrace pairs).getLast? = some (resultFinal pairs) := by
  simp only [resultTrace, List.getLast?_append, PSTRTMCompareErase058.erase_last, Option.some_or, resultFinal]

theorem result_length (pairs : List (Bool × Bool)) : (resultTrace pairs).length = 12 * pairs.length + 12 := by
  simp only [resultTrace, List.length_append, List.length_map, PSTRTMCompareTrace055.compare_length,
    PSTRTMCompareErase058.erase_length, List.length_reverse, pairedDigits_length]
  omega

theorem result_chain (pairs : List (Bool × Bool)) :
    (resultTrace pairs).IsChain (fun before after => Turing.TM0.step resultMachine before = some after) := by
  apply (kernel_chain _ (PSTRTMCompareTrace055.compare_chain 0 [] [] pairs [])).append
    (PSTRTMCompareErase058.erase_chain _ _ 2)
  intro before hb after ha
  simp only [List.getLast?_map, PSTRTMCompareTrace055.compare_last, Option.map_some,
    Option.mem_some_iff, List.append_nil] at hb
  simp only [PSTRTMCompareErase058.erase_head, Option.mem_some_iff] at ha
  subst before
  subst after
  rw [leftColumns_reverse]
  exact kernel_erase_transfer _ _ 2

theorem result_runs (pairs : List (Bool × Bool)) :
    Runs resultMachine (PSTRTMBinaryAdd024.operandColumns pairs) (resultTrace pairs) (resultFinal pairs) := by
  apply PSTRTMTrace002.runs_of_chain
  · simpa [Turing.TM0.init, state, Turing.Tape.mk₁] using result_head pairs
  · exact result_chain pairs
  · exact result_last pairs
  · exact result_halt _ _

theorem result_final_tape (pairs : List (Bool × Bool)) :
    (resultFinal pairs).Tape = Turing.Tape.mk₁ (outputWord (PSTRTMCompareCode054.resultRelation 0 pairs)) :=
  PSTRTMCompareErase058.output_tape _

theorem operandColumns_length (pairs : List (Bool × Bool)) :
    (PSTRTMBinaryAdd024.operandColumns pairs).length = 4 * pairs.length := by
  induction pairs with
  | nil => rfl
  | cons pair later ih =>
    obtain ⟨a,b⟩ := pair
    change (a :: true :: b :: true :: PSTRTMBinaryAdd024.operandColumns later).length = _
    simp only [List.length_cons, ih]
    omega

/-- Isolated packed comparator, with ENTIRE output tape canonical and all
earlier input cells actually erased. The nondestructive framed kernel remains
available separately; destructive cleanup does not claim an archive frame. -/
theorem result_computes (pairs : List (Bool × Bool)) :
    computes resultMachine (PSTRTMBinaryAdd024.operandColumns pairs)
      (outputWord (PSTRTMCompareCode054.resultRelation 0 pairs))
      (12 * pairs.length + 12) (28 * pairs.length + 25) := by
  refine ⟨resultTrace pairs, resultFinal pairs, result_runs pairs, ?_, ?_, ?_⟩
  · rw [result_final_tape]
    simp [Turing.Tape.mk₁, Turing.Tape.mk₂]
  · exact (result_length pairs).le
  · have hs := PSTRTMTrace002.visitedSpace_le resultMachine
      (PSTRTMBinaryAdd024.operandColumns pairs).length (resultTrace pairs)
    rw [operandColumns_length, result_length] at hs
    rw [operandColumns_length]
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCompareRun059
