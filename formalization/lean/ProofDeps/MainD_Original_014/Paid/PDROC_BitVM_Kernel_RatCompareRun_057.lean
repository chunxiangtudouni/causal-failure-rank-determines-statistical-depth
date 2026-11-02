module

public import Paid.PDROC_BitVM_Kernel_RatCompareResources_056

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.Kernel.RatCompare

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

/-- ONE complete genuine comparison path. The uniform native subtraction
contract describes a fixed old machine, not an additional per-input
answer. Its SAME actual final target supplies the five captured flags,
the REAL observedEntry load supplies BoolCell's bit, and actual RawWrite
replaces that target only after both original source operands were read. -/
theorem runs {states : ℕ} (machine : Machine states) (comparison : Comparison) (c d : ℕ)
    (contract : RawOp.NativeContract machine (fun x y => x - y) c d)
    (logical : PaperProofs.Paid.Computation.State) (target left right : Register) (x y : Rat)
    (contents : Stack → List Bool)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (leftRat : logical.register left = .rational x) (rightRat : logical.register right = .rational y)
    (empty0 : contents 0 = []) (empty24 : contents 24 = []) :
    ∃ (run : List (State states)) (final : State states),
      run.head? = some (before states contents) ∧
      run.IsChain (fun a b => TM2.step (program machine comparison target left right) a = some b) ∧
      run.getLast? = some final ∧ TM2.step (program machine comparison target left right) final = none ∧
      final.stk (registerSlot target) = encodeCellBits (.natural (if comparison.rat x y then 1 else 0)) ∧
      final.stk 0 = [] ∧ final.stk 24 = [] ∧ final.stk 25 = [] ∧ final.stk 29 = [] ∧
      run.length ≤ budget machine logical target left right x y c d contents ∧
      ∀ role, role ≠ 0 → role ≠ 24 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target →
        final.stk role = contents role := by
  obtain ⟨difference, differenceLast, differenceHead, differenceChain, differenceEnd, differenceHalt,
    differenceCell, difference0, difference24, difference25, difference29, differenceTime, occupied, differenceFrame⟩ :=
    difference_resources machine c d contract logical target left right x y contents represented leftRat rightRat empty0 empty24
  obtain ⟨first, computed, firstHead, firstChain, firstLast, computedLabel, computedData, _computedStore, firstTime⟩ :=
    CallFamily.actual_return_trace LocalLabel (LocalStore states) (source machine target left right)
      (resume states comparison) 0 (fun other => (initialized states) other.val)
      difference (lowerBefore states 0 contents) differenceLast differenceHead differenceChain differenceEnd differenceHalt
  have firstStart : CallFamily.cfg LocalLabel (LocalStore states) 0
      (fun other => (initialized states) other.val) (lowerBefore states 0 contents) = before states contents := by
    rw [initialized_cfg, initial_cfg]
  rw [firstStart] at firstHead
  obtain ⟨inspector, inspectorHead, inspectorChain, inspectorLast, inspectorHalt, inspectorTime⟩ :=
    Branch.runs (registerSlot target) computed.stk default
  let inspected : Branch.State := ⟨none, Branch.captured (computed.stk (registerSlot target)), computed.stk⟩
  obtain ⟨second, read, secondHead, secondChain, secondLast, readLabel, readData, readStore, secondTime⟩ :=
    CallFamily.actual_return_trace LocalLabel (LocalStore states) (source machine target left right)
      (resume states comparison) 1 (fun other => computed.var other.val) inspector
      (lowerBefore states 1 computed.stk) inspected inspectorHead inspectorChain inspectorLast inspectorHalt
  have readStacks : read.stk = computed.stk := readData
  let inspectorStart := entryState states 1 computed.var computed.stk
  have secondStart : CallFamily.cfg LocalLabel (LocalStore states) 1
      (fun other => computed.var other.val) (lowerBefore states 1 computed.stk) = inspectorStart :=
    initialized_cfg states 1 computed.var computed.stk
  rw [secondStart] at secondHead
  have edge01 : TM2.step (program machine comparison target left right) computed = some inspectorStart := by
    rcases computed with ⟨label, finiteStore, physical⟩
    change label = some (CallFamily.returnLabel LocalLabel 0) at computedLabel
    subst label
    exact advance_zero machine comparison target left right finiteStore physical
  have bridge01 : [computed, inspectorStart].IsChain
      (fun a b => TM2.step (program machine comparison target left right) a = some b) :=
    List.isChain_cons_cons.mpr ⟨edge01, List.isChain_singleton _⟩
  have frontChain := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain first computed [inspectorStart] firstLast firstChain bridge01
  have frontLast : (first ++ [inspectorStart]).getLast? = some inspectorStart :=
    List.getLast?_append_cons first inspectorStart []
  let beforeObserved := (first ++ [inspectorStart]) ++ second.tail
  have beforeObservedChain : beforeObserved.IsChain
      (fun a b => TM2.step (program machine comparison target left right) a = some b) :=
    PDROC.BitVM.Log.TwoStack.join_chain (first ++ [inspectorStart]) second inspectorStart
      frontChain secondChain frontLast secondHead
  have beforeObservedLast : beforeObserved.getLast? = some read :=
    RawInstruction.overlap_last (first ++ [inspectorStart]) second inspectorStart read
      frontLast secondHead secondLast
  have captured : read.var 1 = Branch.captured (encodeCellBits (.rational (x - y))) := by
    rw [readStore, selected_store]
    change Branch.captured (computed.stk (registerSlot target)) = _
    rw [computedData, differenceCell]
  have flag : CompareFlag.flag comparison (read.var 1) = comparison.rat x y := by
    rw [captured]
    simpa only [List.append_nil] using CompareFlag.difference comparison x y []
  let signal := CompareFlag.flag comparison (read.var 1)
  have read0 : read.stk 0 = [] := by rw [readStacks, computedData]; exact difference0
  obtain ⟨boolean, booleanLast, booleanHead, booleanChain, booleanEnd, booleanHalt, _booleanStore,
    booleanWord, booleanTime, booleanFrame⟩ := BoolCell.runs read.stk signal
  obtain ⟨third, booled, thirdHead, thirdChain, thirdLast, booledLabel, booledData, _booledStore, thirdTime⟩ :=
    CallFamily.actual_return_trace LocalLabel (LocalStore states) (source machine target left right)
      (resume states comparison) 2 (fun other => read.var other.val) boolean
      (BoolCell.before read.stk signal) booleanLast booleanHead booleanChain booleanEnd booleanHalt
  let booleanStart := observedState states comparison read.var read.stk
  have thirdStart : CallFamily.cfg LocalLabel (LocalStore states) 2 (fun other => read.var other.val)
      (BoolCell.before read.stk signal) = booleanStart := observed_cfg states comparison read.var read.stk
  rw [thirdStart] at thirdHead
  have edge12 : TM2.step (program machine comparison target left right) read = some booleanStart := by
    rcases read with ⟨label, finiteStore, physical⟩
    change label = some (CallFamily.returnLabel LocalLabel 1) at readLabel
    subst label
    exact advance_observed machine comparison target left right finiteStore physical
  have bridge12 : [read, booleanStart].IsChain
      (fun a b => TM2.step (program machine comparison target left right) a = some b) :=
    List.isChain_cons_cons.mpr ⟨edge12, List.isChain_singleton _⟩
  have middleChain := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain beforeObserved read [booleanStart]
    beforeObservedLast beforeObservedChain bridge12
  have middleLast : (beforeObserved ++ [booleanStart]).getLast? = some booleanStart :=
    List.getLast?_append_cons beforeObserved booleanStart []
  let beforeWriter := (beforeObserved ++ [booleanStart]) ++ third.tail
  have beforeWriterChain : beforeWriter.IsChain
      (fun a b => TM2.step (program machine comparison target left right) a = some b) :=
    PDROC.BitVM.Log.TwoStack.join_chain (beforeObserved ++ [booleanStart]) third booleanStart
      middleChain thirdChain middleLast thirdHead
  have beforeWriterLast : beforeWriter.getLast? = some booled :=
    RawInstruction.overlap_last (beforeObserved ++ [booleanStart]) third booleanStart booled
      middleLast thirdHead thirdLast
  have boolWord : booled.stk 0 = encodeCellBits (BoolCell.value signal) ++ [] := by
    rw [booledData, booleanWord, read0]
  obtain ⟨writer, writerLast, writerHead, writerChain, writerEnd, writerHalt, writerCell, writer0, writer24,
    writer25, writer29, writerTime, writerFrame⟩ := RawWrite.runs target (BoolCell.value signal) [] booled.stk default boolWord
  obtain ⟨fourth, returned, fourthHead, fourthChain, fourthLast, returnedLabel, returnedData, _returnedStore, fourthTime⟩ :=
    CallFamily.actual_return_trace LocalLabel (LocalStore states) (source machine target left right)
      (resume states comparison) 3 (fun other => booled.var other.val) writer
      (lowerBefore states 3 booled.stk) writerLast writerHead writerChain writerEnd writerHalt
  let writerStart := entryState states 3 booled.var booled.stk
  have fourthStart : CallFamily.cfg LocalLabel (LocalStore states) 3 (fun other => booled.var other.val)
      (lowerBefore states 3 booled.stk) = writerStart := initialized_cfg states 3 booled.var booled.stk
  rw [fourthStart] at fourthHead
  have edge23 : TM2.step (program machine comparison target left right) booled = some writerStart := by
    rcases booled with ⟨label, finiteStore, physical⟩
    change label = some (CallFamily.returnLabel LocalLabel 2) at booledLabel
    subst label
    exact advance_two machine comparison target left right finiteStore physical
  have bridge23 : [booled, writerStart].IsChain
      (fun a b => TM2.step (program machine comparison target left right) a = some b) :=
    List.isChain_cons_cons.mpr ⟨edge23, List.isChain_singleton _⟩
  have allFrontChain := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain beforeWriter booled [writerStart]
    beforeWriterLast beforeWriterChain bridge23
  have allFrontLast : (beforeWriter ++ [writerStart]).getLast? = some writerStart :=
    List.getLast?_append_cons beforeWriter writerStart []
  let allCalls := (beforeWriter ++ [writerStart]) ++ fourth.tail
  have allChain : allCalls.IsChain (fun a b => TM2.step (program machine comparison target left right) a = some b) :=
    PDROC.BitVM.Log.TwoStack.join_chain (beforeWriter ++ [writerStart]) fourth writerStart
      allFrontChain fourthChain allFrontLast fourthHead
  have allLast : allCalls.getLast? = some returned :=
    RawInstruction.overlap_last (beforeWriter ++ [writerStart]) fourth writerStart returned allFrontLast fourthHead fourthLast
  let final : State states := ⟨none, returned.var, returned.stk⟩
  have finalEdge : TM2.step (program machine comparison target left right) returned = some final := by
    rcases returned with ⟨label, finiteStore, physical⟩
    change label = some (CallFamily.returnLabel LocalLabel 3) at returnedLabel
    subst label
    exact finish machine comparison target left right finiteStore physical
  have finalPair : [returned, final].IsChain
      (fun a b => TM2.step (program machine comparison target left right) a = some b) :=
    List.isChain_cons_cons.mpr ⟨finalEdge, List.isChain_singleton _⟩
  have actual := PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain allCalls returned [final] allLast allChain finalPair
  let Q := RawInstruction.budget machine logical left right x y c d contents
  let D := NatInstruction.dataSize contents + differenceCap machine target left right * Q
  have member : differenceLast ∈ difference := List.mem_of_mem_getLast? (by rw [differenceEnd]; rfl)
  have targetBound : (booled.stk (registerSlot target)).length ≤ D := by
    rw [booledData, booleanFrame _ (by cases target <;> decide), readStacks, computedData]
    exact occupied differenceLast member (registerSlot target)
  have bool24 : booled.stk 24 = [] := by
    rw [booledData, booleanFrame 24 (by decide), readStacks, computedData]
    exact difference24
  have bool25 : booled.stk 25 = [] := by
    rw [booledData, booleanFrame 25 (by decide), readStacks, computedData]
    exact difference25
  have bool29 : booled.stk 29 = [] := by
    rw [booledData, booleanFrame 29 (by decide), readStacks, computedData]
    exact difference29
  have boolLength : (booled.stk 0).length = 4 := by
    rw [boolWord, List.append_nil]
    cases signal <;> rfl
  have writerSize : RawWrite.inputSize target booled.stk ≤ D + 4 := by
    dsimp only [RawWrite.inputSize]
    rw [bool24, bool25, bool29, boolLength]
    simp only [List.length_nil]
    omega
  have writerBound : writer.length ≤ 64 * (D + 5) :=
    writerTime.trans (Nat.mul_le_mul_left 64 (by omega))
  refine ⟨allCalls ++ [final], final, ?_, actual, List.getLast?_append_cons allCalls final [], rfl,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [allCalls, beforeWriter, beforeObserved, List.head?_append, firstHead, Option.some_or]
  · change returned.stk (registerSlot target) = _
    rw [returnedData, writerCell]
    change encodeCellBits (.natural (if signal then 1 else 0)) = _
    exact congrArg (fun bit : Bool => encodeCellBits (.natural (if bit then 1 else 0))) flag
  · change returned.stk 0 = []
    rw [returnedData]
    exact writer0
  · change returned.stk 24 = []
    rw [returnedData]
    exact writer24
  · change returned.stk 25 = []
    rw [returnedData]
    exact writer25
  · change returned.stk 29 = []
    rw [returnedData]
    exact writer29
  · have firstBound : first.length ≤ Q := firstTime.le.trans differenceTime
    have secondBound : second.length = 2 := secondTime.trans inspectorTime
    have thirdBound : third.length = 2 := thirdTime.trans booleanTime
    have fourthBound : fourth.length ≤ 64 * (D + 5) := fourthTime.le.trans writerBound
    simp only [allCalls, beforeWriter, beforeObserved, List.length_append, List.length_tail, List.length_cons, List.length_nil]
    change _ ≤ Q + 64 * (D + 5) + 8
    omega
  · intro role not0 not24 not25 not29 notTarget
    change returned.stk role = contents role
    rw [returnedData, writerFrame role not0 not24 not25 not29 notTarget,
      booledData, booleanFrame role not0, readStacks, computedData]
    exact differenceFrame role not0 not24 not25 not29 notTarget

end PDROC.BitVM.Kernel.RatCompare
