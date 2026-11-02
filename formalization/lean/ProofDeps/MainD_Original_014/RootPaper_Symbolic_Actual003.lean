module
public import RootPaper_Symbolic_Selection002
public import RootL01_PHCompat_Public007

/-! The paper's actual P/H-to-symbolic-expression theorem. The caller supplies
only the original instance, original rational statistical input and available
tools. The head count is READ FROM the same actual H output heap. No assumed
correct head list, free coefficient, numerical KL oracle or Bool VM occurs.
-/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootPaper.Symbolic
open PaperProofs.Common PaperProofs.Common.SymbolicPrice PaperProofs.Statistics PaperProofs.Structure
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims PA17A19RuntimeEntry020 PSTRHeadsRuntime
open PaperProofs.Common.Native.CompactPrice
open RootL01.PHCompat.Assembly

variable {I : Instance}

def decodeDepth (q code : Nat) : ℕ∞ := if code = q + 2 then ⊤ else code

theorem decode_original_depth (q : Nat) (full : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    decodeDepth q (encodeRank q (errorRank full remaining)) = errorRank full remaining := by
  by_cases infinite : errorRank full remaining = ⊤
  · simp only [decodeDepth, encodeRank, infinite, ite_true]
  · have bound := IndexedQuery.errorRank_finite_le_q_add_one q full remaining infinite
    obtain ⟨value, valueEq⟩ := ENat.ne_top_iff_exists.mp infinite
    have small : value ≤ q + 1 := ENat.natCast_le_natCast.mp (valueEq.symm ▸ bound)
    rw [← valueEq]
    simp only [encodeRank, ENat.natCast_ne_top, ite_false, ENat.toNat_natCast, decodeDepth]
    split_ifs with impossible
    · omega
    · rfl

structure PaperOutput where
  depthCode : Nat
  indices : List Nat
  built : Built

/-- Charge six header/metadata navigations and every word read into the input view
as well as the counted recursive index/experiment construction. Existing H
already paid for producing these words; this is a separate consumer charge. -/
def fromHeadWords (input : StatisticalInput I) (words : List Nat) : PaperOutput :=
  ⟨words.headD 0, words.drop 2, navigate (words.length + 6) (fromIndices input (words.drop 2))⟩

structure PaperSpec (input : StatisticalInput I) (available : Finset I.Tool)
    (output : PaperOutput) : Prop where
  depth_exact : output.depthCode = encodeRank I.toolCount (errorRank I.compatibility available)
  decoded_depth : decodeDepth I.toolCount output.depthCode = errorRank I.compatibility available
  indices_exact : output.indices = criticalIndices I.toolCount I.compatibility (Finset.univ \ available)
  original_order : output.indices = (inputHeads input available).map Prod.fst
  head_count : output.indices.length ≤ I.stageCount
  no_duplicates : output.indices.Nodup
  valid_indices : ∀ index ∈ output.indices, index < I.stageCount
  coefficient_exact : output.built.expression.eval = input.orderedCoefficient available
  nodes_exact : output.built.expression.nodes =
    1 + ((inputHeads input available).map (fun entry => 14 * entry.2.alphabetSize + 14)).sum
  construction_work : output.built.work ≤ 96 * ((symbolicInput input available).length + 1) ^ 2
  node_and_leaf_size : output.built.expression.nodes + leafBits output.built.expression ≤
    96 * ((symbolicInput input available).length + 1) ^ 2
  /-- Five constructor kinds fit in three bits each. Rational leaf payloads
  retain their supplied finite sign/numerator/denominator representation. -/
  symbolic_bit_size : 3 * output.built.expression.nodes + leafBits output.built.expression ≤
    288 * ((symbolicInput input available).length + 1) ^ 2

theorem headWords_drop (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    (headWords q full used).drop 2 = criticalIndices q full used := by
  simp only [headWords, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero]

theorem paper_from_original_headWords (hl : LaminarSchedule I.compatibility)
    (input : StatisticalInput I) (available : Finset I.Tool) :
    PaperSpec input available
      (fromHeadWords input (headWords I.toolCount I.compatibility (Finset.univ \ available))) := by
  have order := PSTRHeads.criticalIndices_inputHeads hl input available
  have count := PSTRHeads.criticalIndices_length_le I.toolCount I.compatibility (Finset.univ \ available)
  have work := fromIndices_work_le input available
    (criticalIndices I.toolCount I.compatibility (Finset.univ \ available)) count
  have words := PSTRHeads.headWords_length_le I.toolCount I.compatibility (Finset.univ \ available)
  have stages := PSTRSymbolicBits.stageCount_le_input_length input available
  have remaining : (Finset.univ \ (Finset.univ \ available) : Finset I.Tool) = available := by
    ext tool
    simp
  have workBound :
      (fromHeadWords input (headWords I.toolCount I.compatibility (Finset.univ \ available))).built.work ≤
        96 * ((symbolicInput input available).length + 1) ^ 2 := by
    simp only [fromHeadWords, navigate, Built.work, headWords_drop]
    simp only [Built.work] at work
    change (headWords I.toolCount I.compatibility (Finset.univ \ available)).length ≤ I.stageCount + 2 at words
    nlinarith
  have size := (Built.output_le_work
    (fromHeadWords input (headWords I.toolCount I.compatibility (Finset.univ \ available))).built).trans workBound
  have depth :
      (fromHeadWords input (headWords I.toolCount I.compatibility (Finset.univ \ available))).depthCode =
        encodeRank I.toolCount (errorRank I.compatibility available) := by
    simp only [fromHeadWords, headWords, List.cons_append, List.nil_append,
      List.headD_cons, PSTRCallback.callback_rank I.toolCount I.compatibility hl,
      List.drop_zero, remaining]
  refine ⟨depth, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, workBound, size, ?_⟩
  · rw [depth]
    exact decode_original_depth _ _ _
  · exact headWords_drop _ _ _
  · exact (headWords_drop _ _ _).trans order
  · simpa only [fromHeadWords, headWords_drop, Instance.stageCount] using count
  · simpa only [fromHeadWords, headWords_drop] using
      PSTRHeads.criticalIndices_nodup I.toolCount I.compatibility (Finset.univ \ available)
  · intro index member
    have h : index ∈ criticalIndices I.toolCount I.compatibility (Finset.univ \ available) := by
      simpa only [fromHeadWords, headWords_drop] using member
    exact PSTRHeads.criticalIndices_mem_lt _ _ _ h
  · change (fromIndices input ((headWords I.toolCount I.compatibility (Finset.univ \ available)).drop 2)).expression.eval = _
    rw [headWords_drop, order]
    exact from_original_heads_eval input available
  · change (fromIndices input ((headWords I.toolCount I.compatibility (Finset.univ \ available)).drop 2)).expression.nodes = _
    rw [headWords_drop, order]
    exact from_original_heads_nodes input available
  · omega

/-- Read the actual count word at offset 1, then read exactly count+2 words.
The consumer is not supplied a mathematical expected output length. -/
def readHeadWords {bits : Nat} (heap : BitVec bits → BitVec bits) (base : Nat) : List Nat :=
  let count := (heap (BitVec.ofNat bits (base + 1))).toNat
  heapWordsAt heap base (count + 2)

theorem heap_word_of_words {bits : Nat} (heap : BitVec bits → BitVec bits)
    (base : Nat) (words : List Nat) (exactWords : heapWordsAt heap base words.length = words)
    (position : Nat) (valid : position < words.length) :
    (heap (BitVec.ofNat bits (base + position))).toNat = words.getD position 0 := by
  have inputLength : position < (heapWordsAt heap base words.length).length := by
    simpa only [heapWordsAt, List.length_map, List.length_range] using valid
  have equal := congrArg (fun xs => xs.getD position 0) exactWords
  rw [List.getD_eq_getElem _ _ inputLength, List.getD_eq_getElem _ _ valid] at equal
  rw [List.getD_eq_getElem _ _ valid]
  simpa only [heapWordsAt, List.getElem_map, List.getElem_range] using equal

theorem read_actual_heads {q bits : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (heap : BitVec bits → BitVec bits) (base : Nat)
    (actual : heapWordsAt heap base (headWords q full used).length = headWords q full used) :
    readHeadWords heap base = headWords q full used := by
  have countWord := heap_word_of_words heap base (headWords q full used) actual 1 (by
    simp only [headWords, List.length_append, List.length_cons, List.length_nil]
    omega)
  have count : (heap (BitVec.ofNat bits (base + 1))).toNat = (criticalIndices q full used).length := by
    simpa only [headWords, List.cons_append, List.nil_append, List.getD_cons_succ,
      List.getD_cons_zero] using countWord
  rw [readHeadWords, count]
  have length : (headWords q full used).length = (criticalIndices q full used).length + 2 := by
    simp only [headWords, List.length_append, List.length_cons, List.length_nil]
    omega
  rw [length] at actual
  exact actual

/-- Complete paper-scope construction on the same P-produced heap. This
theorem DISCHARGES head correctness using the already proved original P/H
program theorem; it does not accept correct heads as a new caller oracle.
The first five cost/correctness conjuncts are exactly original P and H.
The final conjunct proves the explicit consumer's exact symbolic result,
node/payload-bit size and its separate polynomial construction-work bound. -/
theorem actual_original_paper_symbolic (hl : LaminarSchedule I.compatibility)
    (input : StatisticalInput I) (available : Finset I.Tool) :
    ∃ prepSteps headSteps : Nat,
      DynamicRunCorrect (allocatedWords I.compatibility)
        (controllerInput I.toolCount I.compatibility (Finset.univ \ available))
        RootL01.PHCompat.Preparation.program prepSteps (fun _ => BitVec.ofNat (wordBits I.compatibility) 0) ∧
      totalCost (allocatedWords I.compatibility)
        (controllerInput I.toolCount I.compatibility (Finset.univ \ available))
        RootL01.PHCompat.Preparation.program prepSteps (fun _ => BitVec.ofNat (wordBits I.compatibility) 0) ≤
        RootL01.PHCompat.Preparation.constant *
          preprocessingWork I.compatibility.length I.toolCount (treeSize I.toolCount I.compatibility) ∧
      headSteps ≤ (I.compatibility.length + 1) * (PSTRUniformQuery.budget I.compatibility + 101) ∧
      DynamicRunCorrect (allocatedWords I.compatibility) (callInput I.toolCount I.compatibility .query)
        PSTRUniformHeads.program headSteps (preparedHeap I.compatibility (Finset.univ \ available) prepSteps) ∧
      callCost I.toolCount I.compatibility PSTRUniformHeads.program .query headSteps
        (preparedHeap I.compatibility (Finset.univ \ available) prepSteps) ≤ 30000 * headWork I.toolCount I.compatibility ∧
      (let after := packingRun (callInput I.toolCount I.compatibility .query) PSTRUniformHeads.program headSteps
          (packingInitial (preparedHeap I.compatibility (Finset.univ \ available) prepSteps));
        HeapRepresents I.toolCount I.compatibility (capacity I.compatibility)
          ⟨I.compatibility.length, Finset.univ \ available, false⟩ after.heap ∧
        (after.register .index).toNat + (headWords I.toolCount I.compatibility (Finset.univ \ available)).length ≤
          allocatedWords I.compatibility ∧
        readHeadWords after.heap (after.register .index).toNat =
          headWords I.toolCount I.compatibility (Finset.univ \ available) ∧
        PaperSpec input available (fromHeadWords input (readHeadWords after.heap (after.register .index).toNat))) := by
  obtain ⟨prepSteps, headSteps, prepCorrect, prepCost, headTime, headCorrect, headCost, output⟩ :=
    RootL01.PHCompat.Public.actual_original_prepared_query I.compatibility hl (Finset.univ \ available)
  refine ⟨prepSteps, headSteps, prepCorrect, prepCost, headTime, headCorrect, headCost, ?_⟩
  dsimp only at output ⊢
  obtain ⟨represented, range, actual⟩ := output
  have words := read_actual_heads I.compatibility (Finset.univ \ available) _ _ actual
  exact ⟨represented, range, words, words.symm ▸ paper_from_original_headWords hl input available⟩

end RootPaper.Symbolic
