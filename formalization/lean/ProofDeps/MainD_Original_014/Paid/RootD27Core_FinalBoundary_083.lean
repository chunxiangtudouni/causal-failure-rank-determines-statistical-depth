module

public import Paid.RootD27Core_ComparisonDecision_082
public import Paid.PDCompute_CoreEmit_Resources_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

theorem original_solution_encoding (P : Parameters) (fee : ℚ) (solution : MultiplierSolve)
    (original : OriginalSolved P fee solution) :
    originalSolveEncoding P fee solution.multiplier=encodeTable solution.table :=
  congrArg (fun computed : MultiplierSolve=>encodeTable computed.table) original.symm

/-- The emitter's input facts come from the actual retained original
table, including its real encoded length; no output payload is supplied. -/
theorem SolvedBuffer.emit_payload {P : Parameters} {fee : ℚ} {solution : MultiplierSolve}
    {side : Bool} {state : State} (buffer : SolvedBuffer P fee solution.multiplier side state)
    (original : OriginalSolved P fee solution) :
    PDCompute.CoreEmit.SolvePayload state P.certificate.stages P.tools P.certificate.M side solution := by
  have encoding:=original_solution_encoding P fee solution original
  refine ⟨buffer.1,?_,?_⟩
  · simpa only [encoding,PDCompute.CoreEmit.lengthSlot,tableLengthSlot] using buffer.2.2.1
  · simpa only [encoding,PDCompute.CoreEmit.bufferBase] using buffer.2.2.2

theorem SearchStateRep.emit_payload {P : Parameters} {fee : ℚ} {source : MultiplierState}
    {state : State} (represented : SearchStateRep P fee state source) :
    PDCompute.CoreEmit.StatePayload state P.certificate.stages P.tools P.certificate.M source := by
  cases source with
  | exact solution => exact ⟨represented.2.1,represented.2.2.emit_payload represented.1⟩
  | bracket lower upper =>
    exact ⟨represented.2.2.1,represented.2.2.2.1.emit_payload represented.1,
      represented.2.2.2.2.emit_payload represented.2.1⟩

private theorem singleton_of_cell (state : State) (address : ℕ) (value : Cell)
    (live : address∈state.live) (stored : state.heap address=value) : HeapList state address [value] := by
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simpa only [Nat.add_zero] using live
  · intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simpa only [Nat.add_zero,List.getElem_cons_zero] using stored

theorem prepared_emit_dimensions (P : Parameters) (fee : ℚ) (state : State)
    (prepared : HeapList state 0 (preparedInput P fee)) :
    PDCompute.CoreEmit.PreparedDimensions state P.certificate.stages P.tools P.certificate.M := by
  have live (index : ℕ) (inside : index<13) : index∈state.live := by
    simpa only [Nat.zero_add] using prepared.1 index inside
  have nValue:=PDLower.CalibrationCompute.HeapList.value prepared 0 (by change 0<13;decide)
  have kValue:=PDLower.CalibrationCompute.HeapList.value prepared 1 (by change 1<13;decide)
  have mValue:=PDLower.CalibrationCompute.HeapList.value prepared 7 (by change 7<13;decide)
  change state.heap 0=.natural P.certificate.stages at nValue
  change state.heap 1=.natural P.tools at kValue
  change state.heap 7=.natural P.certificate.M at mValue
  exact ⟨singleton_of_cell state 0 _ (live 0 (by decide)) nValue,
    singleton_of_cell state 1 _ (live 1 (by decide)) kValue,
    singleton_of_cell state 7 _ (live 7 (by decide)) mValue⟩

private theorem original_emit_end (P : Parameters) (fee : ℚ) (solution : MultiplierSolve)
    (side : Bool) (original : OriginalSolved P fee solution) :
    PDCompute.CoreEmit.bufferBase P.certificate.stages P.tools P.certificate.M side+
      (encodeTable solution.table).length≤99+2*P.certificate.M+78*PDCompute.Solver.entryCount P.certificate.stages P.tools := by
  have encoding:=original_solution_encoding P fee solution original
  have capacity:=(original_table_capacity P fee solution.multiplier P.certificate.stages P.tools).trans
    (retained_capacity_enough P.certificate.stages P.tools)
  change (originalSolveEncoding P fee solution.multiplier).length≤retainedTableCapacity P.certificate.stages P.tools at capacity
  rw [encoding] at capacity
  unfold retainedTableCapacity at capacity
  unfold PDCompute.CoreEmit.bufferBase retainedTableBase
  cases side <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

/-- Both actual physical buffer ends fit the original one-workspace
address cap, uniformly for every reachable original source state. -/
theorem SearchStateRep.emit_ends {P : Parameters} {fee : ℚ} {source : MultiplierState}
    {state : State} (represented : SearchStateRep P fee state source) :
    PDCompute.CoreEmit.StateEndBound P.certificate.stages P.tools P.certificate.M
      (99+2*P.certificate.M+78*PDCompute.Solver.entryCount P.certificate.stages P.tools) source := by
  cases source with
  | exact solution => exact original_emit_end P fee solution false represented.1
  | bracket lower upper =>
    exact ⟨original_emit_end P fee lower false represented.1,original_emit_end P fee upper true represented.2.1⟩

theorem selectorZero_length : (headerCode selectorZeroCommands).length=4:=rfl

/-- The actual final selector first inspects the original zero-charge
risk, then the source tag. Both zero-risk and exact cases write0; only
the remaining bracket case executes the full current-weight computation. -/
def finalSelectorCode (origin : ℕ) : List Instruction :=
  comparisonDecisionCode .lessEqual 12 3 (origin+11) (origin+176)++
    tagDecisionCode (origin+11) (origin+176)++
    finalBracketCode (origin+15)++[.jump (origin+180)]++headerCode selectorZeroCommands

theorem finalSelector_length (origin : ℕ) : (finalSelectorCode origin).length=180 := by
  simp only [finalSelectorCode,List.length_append,comparisonDecision_length,tagDecision_length,
    finalBracketCode_length,List.length_cons,List.length_nil,selectorZero_length]

def finalizationCode (origin : ℕ) : List Instruction :=
  finalSelectorCode origin++PDCompute.CoreEmit.stateCode (origin+180) (origin+248)++
    PDCompute.CoreEmit.outputSlotCode 29++[.halt]

theorem finalization_length (origin : ℕ) : (finalizationCode origin).length=252 := by
  simp only [finalizationCode,List.length_append,finalSelector_length,PDCompute.CoreEmit.state_length,
    PDCompute.CoreEmit.outputSlot_length,List.length_cons,List.length_nil]

theorem finalSelector_fetch_parts (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (finalSelectorCode origin)) :
    FetchesCode program origin (comparisonDecisionCode .lessEqual 12 3 (origin+11) (origin+176)) ∧
    FetchesCode program (origin+11) (tagDecisionCode (origin+11) (origin+176)) ∧
    FetchesCode program (origin+15) (finalBracketCode (origin+15)) ∧
    program[origin+175]?=some (.jump (origin+180)) ∧
    FetchesCode program (origin+176) (headerCode selectorZeroCommands) := by
  change FetchesCode program origin
    (comparisonDecisionCode .lessEqual 12 3 (origin+11) (origin+176)++
      tagDecisionCode (origin+11) (origin+176)++finalBracketCode (origin+15)++
      [.jump (origin+180)]++headerCode selectorZeroCommands) at fetched
  simp only [List.append_assoc] at fetched
  have tagFetch:=fetched.append_right
  have bracketFetch:=tagFetch.append_right
  have jumpFetch:=bracketFetch.append_right
  have zeroFetch:=jumpFetch.append_right
  refine ⟨fetched.append_left,?_,?_,?_,?_⟩
  · simpa only [comparisonDecision_length] using tagFetch.append_left
  · simpa only [comparisonDecision_length,tagDecision_length] using bracketFetch.append_left
  · simpa only [comparisonDecision_length,tagDecision_length,finalBracketCode_length,Nat.add_zero,
      List.getElem?_cons_zero] using jumpFetch.append_left 0 (by change 0<1;decide)
  · simpa only [comparisonDecision_length,tagDecision_length,finalBracketCode_length,List.length_cons,List.length_nil]
      using zeroFetch

end RootD27.Core
