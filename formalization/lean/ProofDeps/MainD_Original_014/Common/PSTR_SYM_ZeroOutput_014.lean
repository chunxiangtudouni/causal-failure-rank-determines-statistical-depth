module

public import Common.PSTR_SYM_OriginalPriorData_012

/-! Exact original N0 output. Terminal rank is TOP, encoded q+2;
there is NO uniform fixed literal output. The Expr is the rational-zero
constructor itself, not merely an expression whose real evaluation is zero. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator

open PaperProofs.Common PaperProofs.Structure.LaminarTree

theorem callback_empty_rank (q : Nat) (stage : Fin 1) (used : Finset (Fin q)) :
    (CompactControllerClaims.callback q [] stage used).rank = ⊤ := by
  by_cases positive : 0 < q
  · simp [CompactControllerClaims.callback, positive, AlgorithmClaims.expectedReply,
      IndexedQuery.terminalReply]
  · simp [CompactControllerClaims.callback, positive]

theorem headWords_empty (q : Nat) (used : Finset (Fin q)) :
    CompactPrice.headWords q [] used = [q + 2,0] := by
  simp [CompactPrice.headWords, CompactPrice.criticalIndices, callback_empty_rank,
    AlgorithmClaims.encodeRank]

theorem inputExpression_zero {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (zero : I.stageCount = 0) :
    SymbolicPrice.inputExpression input available = .rational 0 := by
  have schedule : SymbolicPrice.inputSchedule input = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    simp only [SymbolicPrice.inputSchedule, List.length_ofFn]
    simpa only [Instance.stageCount] using zero
  simp only [SymbolicPrice.inputExpression, schedule, SymbolicPrice.leadingExpression]
  split_ifs
  · rfl
  · simp only [SymbolicPrice.headExpression, SymbolicPrice.heads, List.map_nil, SymbolicPrice.sumExpr]

def zeroOutput (q : Nat) : List Bool :=
  encode [.natural (q + 2), .natural 0, .natural 0, .rational 0]

theorem original_zero_output {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (zero : I.stageCount = 0) :
    CompactPrice.symbolicOutput input available = zeroOutput I.toolCount := by
  have empty : I.compatibility = [] := List.eq_nil_iff_length_eq_zero.mpr
    (by simpa only [Instance.stageCount] using zero)
  unfold CompactPrice.symbolicOutput
  rw [empty, headWords_empty, inputExpression_zero input available zero]
  rfl

/-- All bits except the raw encodeNat(q+2) field are fixed code literals. -/
def zeroPrefix : List Bool := encodeNat 4 ++ [false]

def zeroSuffix : List Bool :=
  encodeDatum (.natural 0) ++ encodeDatum (.natural 0) ++ encodeDatum (.rational 0) ++ [true]

theorem zeroPrefix_bits :
    zeroPrefix = [true,true,true,false,false,false,true,false] := by decide

theorem zeroSuffix_bits :
    zeroSuffix = [false,true,false,false,false,true,false,false,
      true,false,true,false,false,true,false,true,true] := by decide

theorem zeroOutput_shape (q : Nat) :
    zeroOutput q = zeroPrefix ++ encodeNat (q + 2) ++ zeroSuffix := by
  simp only [zeroOutput, encode, List.length_cons, List.length_nil, List.flatMap_cons,
    List.flatMap_nil, encodeDatum, zeroPrefix, zeroSuffix, List.cons_append,
    List.nil_append, List.append_nil, List.append_assoc]

theorem zeroOutput_length (q : Nat) : (zeroOutput q).length = 2 * natBits (q + 2) + 26 := by
  rw [zeroOutput_shape, List.length_append, List.length_append,
    zeroPrefix_bits, zeroSuffix_bits, PSTRTMLength004.encodeNat_length]
  simp only [List.length_cons, List.length_nil]
  omega

theorem zeroOutput_zero_ne_one : zeroOutput 0 ≠ zeroOutput 1 := by decide

/-- The original N0 outer count already encodes q+2. This is an original
field identity, not a serializer, arithmetic result or new input field. -/
theorem rawInstance_zero {I : Instance} (input : StatisticalInput I) (zero : I.stageCount = 0) :
    rawInstance input = [.natural 0,.natural I.toolCount] := by
  have empty : I.compatibility = [] := List.eq_nil_iff_length_eq_zero.mpr
    (by simpa only [Instance.stageCount] using zero)
  have stages : List.finRange I.compatibility.length = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    simp only [List.length_finRange]
    simpa only [Instance.stageCount] using zero
  have incidence : I.compatibility.flatMap rawSet = [] := by rw [empty]; rfl
  unfold rawInstance
  simp only [Instance.stageCount]
  rw [stages, incidence]
  simp only [List.flatMap_nil, List.append_nil]
  have lengthZero : I.compatibility.length = 0 := by simpa only [Instance.stageCount] using zero
  rw [lengthZero]

theorem zero_original_count {I : Instance} (input : StatisticalInput I)
    (available : Finset I.Tool) (zero : I.stageCount = 0) :
    (rawInstance input ++ rawSet available).length = I.toolCount + 2 := by
  rw [rawInstance_zero input zero]
  simp only [List.length_append, List.length_cons, List.length_nil, rawSet,
    List.length_map, List.length_finRange]
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicLocator
