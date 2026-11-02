module

public import Structure.L01_3_5_TABLE_NatSerializer_Code_019

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_NatSerializer019

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation
open L01_3_5_TABLE_Trace005

def collectEntry {C : Type*} (background : Bank) (context : C) (memory : RatInput.Store)
    (value : Nat) (tail : List Bool) : State C :=
  RatInput.state background 0 context memory (L01_3_5_TABLE_FourRecord011.packet value ++ tail)
    (background 7) [] (background 4) (background 13)

theorem collect_program_pushes {C : Type*} (label : Label) :
    AuxWorkspace.pushes (collectProgram (C := C) label) ≤ 7 := by
  fin_cases label
  · exact (by decide : 1 ≤ 7)
  · simp [collectProgram,RatInput.program,RatInput.fieldBody,AuxWorkspace.pushes]
  · exact Nat.zero_le 7
  · change AuxWorkspace.pushes (LabelMap.statement PSTRSymbolicRatExport.restoreLabel
      (StackIso.statement RatInput.restoreRoles (PSTRSymbolicNaturalExport.program (C := C) 2))) ≤ 7
    rw [LabelMap.statement_pushes,StackIso.statement_pushes]
    exact PSTRSymbolicNaturalExport.source_pushes 2
  · exact Nat.zero_le 7

theorem collect_program_actions {C : Type*} (label : Label) :
    ScannerClock.actions (collectProgram (C := C) label) ≤ 9 := by
  fin_cases label
  · exact (by decide : 1 ≤ 9)
  · simp [collectProgram,RatInput.program,RatInput.fieldBody,ScannerClock.actions]
  · exact Nat.zero_le 9
  · change ScannerClock.actions (LabelMap.statement PSTRSymbolicRatExport.restoreLabel
      (StackIso.statement RatInput.restoreRoles (PSTRSymbolicNaturalExport.program (C := C) 2))) ≤ 9
    rw [LabelMap.statement_actions,StackIso.statement_actions]
    exact PSTRSymbolicNaturalExport.source_actions 2
  · exact Nat.zero_le 9

theorem actual_collect_natural {C : Type*} (background : Bank) (context : C) (memory : RatInput.Store)
    (value : Nat) (tail : List Bool) :
    ∃ (path : List (State C)) (final : State C),
      path.head? = some (collectEntry background context memory value tail) ∧
      path.IsChain (fun before after => TM2.step collectProgram before = some after) ∧
      path.getLast? = some final ∧ final.l = some 4 ∧ final.var.1 = context ∧
      final.stk = Function.update (collectEntry background context memory value tail).stk 3
        (PSTRTMNatValue017.rawPayload value).reverse ∧
      path.length = 3*(PSTRTMNatValue017.rawPayload value).length+7 ∧
      ∀ current ∈ path, current.var.1 = context ∧
        RatInput.occupied current.stk ≤
          4*RatInput.occupied (collectEntry background context memory value tail).stk+8 := by
  rcases memory with ⟨bit,flag,mode⟩
  let digits := PSTRTMNatValue017.rawPayload value
  let copied := false :: false :: (PSTRTMRawNat010.leftBlocks digits).reverse
  let packet := L01_3_5_TABLE_FourRecord011.packet value
  let entry := collectEntry background context (bit,flag,mode) value tail
  have digitsLength : digits.length = (PSTRTMNatValue017.rawPayload value).length := rfl
  have packetShape : packet ++ tail = PSTRTMRawNat010.leftBlocks digits ++ false :: false :: tail := by
    simp only [packet,L01_3_5_TABLE_FourRecord011.packet,digits,List.append_assoc,
      List.cons_append,List.nil_append]
  let middle := RatInput.state background 2 context (false,false,mode) tail
    (PSTRSymbolicNaturalExport.backups copied ++ true :: background 7)
    digits.reverse (background 4) (background 13)
  let restoreStart := RatInput.state background 3 context (false,false,mode) tail
    (PSTRSymbolicNaturalExport.backups copied ++ true :: background 7)
    digits.reverse (background 4) (background 13)
  let final := RatInput.state background 4 context
    (PSTRSymbolicNaturalExport.finalBit copied false,true,mode) (packet ++ tail)
    (background 7) digits.reverse (background 4) (background 13)
  have fieldFirst := RatInput.field_head false background context mode digits bit flag [] tail
    (background 7) [] (background 4) (background 13)
  have fieldLast := RatInput.field_last false background context mode digits bit flag [] tail
    (background 7) [] (background 4) (background 13)
  have fieldLast' : (RatInput.fieldTrace false background context mode digits bit flag [] tail
      (background 7) [] (background 4) (background 13)).getLast? = some middle := by
    simpa only [Bool.false_eq_true,ite_false,List.append_nil] using fieldLast
  let boot : Part collectProgram entry entry := ⟨[entry],rfl,List.isChain_singleton _,rfl⟩
  let field : Part collectProgram
      (RatInput.state background 1 context (bit,flag,mode) (packet ++ tail)
        (true :: background 7) [] (background 4) (background 13)) middle :=
    ⟨RatInput.fieldTrace false background context mode digits bit flag [] tail
      (background 7) [] (background 4) (background 13),
      by
        rw [packetShape]
        simpa only [PSTRSymbolicNaturalExport.backups,List.flatMap_nil,List.nil_append,
          Bool.false_eq_true,ite_false] using fieldFirst,
      field_lift background context mode digits bit flag [] tail (background 7) [] (background 4) (background 13),fieldLast'⟩
  have copiedReverse : copied.reverse ++ tail = packet ++ tail := by
    simp only [copied,packet,L01_3_5_TABLE_FourRecord011.packet,List.reverse_cons,List.reverse_reverse,List.append_assoc]
    rfl
  have restoreLast := RatInput.restore_last background context false false mode copied tail
    (background 7) digits.reverse (background 4) (background 13)
  rw [copiedReverse] at restoreLast
  let restore : Part collectProgram restoreStart final :=
    ⟨RatInput.restoreTrace background context false false mode copied tail
      (background 7) digits.reverse (background 4) (background 13),
      RatInput.restore_head background context false false mode copied tail (background 7) digits.reverse (background 4) (background 13),
      restore_lift background context false false mode copied tail (background 7) digits.reverse (background 4) (background 13),restoreLast⟩
  let all := (boot.append field (prepare_step background context (bit,flag,mode)
    (packet ++ tail) (background 7) [] (background 4) (background 13))).append restore
    (return_step background context (false,false,mode) tail
      (PSTRSymbolicNaturalExport.backups copied ++ true :: background 7) digits.reverse (background 4) (background 13))
  have massEntry : RatInput.occupied (collectEntry background context (bit,flag,mode) value tail).stk = RatInput.baseMass background+
      2*digits.length+2+tail.length+(background 7).length+(background 4).length+(background 13).length := by
    change RatInput.occupied (RatInput.state background 0 context (bit,flag,mode) (packet ++ tail)
      (background 7) [] (background 4) (background 13)).stk = _
    rw [RatInput.occupied_state]
    simp only [packet,L01_3_5_TABLE_FourRecord011.packet,List.length_append,
      RatOutput.flagged_length,List.length_cons,List.length_nil]
    omega
  refine ⟨all.trace,final,all.head,all.chain,all.last,rfl,rfl,?_,?_,?_⟩
  · change RatInput.cells background (packet ++ tail) (background 7) digits.reverse (background 4) (background 13) =
      Function.update (RatInput.cells background (packet ++ tail) (background 7) [] (background 4) (background 13)) 3 digits.reverse
    exact (RatInput.update_numerator background (packet ++ tail) (background 7) []
      (background 4) (background 13) digits.reverse).symm
  · change (([entry] ++ field.trace) ++ restore.trace).length = _
    rw [List.length_append,List.length_append]
    change 1+(RatInput.fieldTrace false background context mode digits bit flag [] tail
      (background 7) [] (background 4) (background 13)).length+
      (RatInput.restoreTrace background context false false mode copied tail
        (background 7) digits.reverse (background 4) (background 13)).length = _
    rw [RatInput.field_length,RatInput.restore_length]
    simp only [copied,List.length_cons,List.length_reverse,RatOutput.flagged_length]
    omega
  · intro current present
    rcases List.mem_append.mp present with before | inRestore
    · rcases List.mem_append.mp before with inBoot | inField
      · have same := List.mem_singleton.mp inBoot
        subst current
        exact ⟨rfl,by
          change RatInput.occupied (collectEntry background context (bit,flag,mode) value tail).stk ≤ _
          omega⟩
      · have frames := RatInput.field_frames false background context mode digits bit flag [] tail
          (background 7) [] (background 4) (background 13) current inField
        have cap := RatInput.field_mass false background context mode digits bit flag [] tail
          (background 7) [] (background 4) (background 13) current inField
        simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at cap
        exact ⟨frames.1,by omega⟩
    · have frames := RatInput.restore_frames background context false false mode copied tail
        (background 7) digits.reverse (background 4) (background 13) current inRestore
      have cap := RatInput.restore_mass background context false false mode copied tail
        (background 7) digits.reverse (background 4) (background 13) current inRestore
      simp only [copied,List.length_cons,List.length_reverse,RatOutput.flagged_length] at cap
      exact ⟨frames.1,by omega⟩

end PaperProofs.Common.Native.L01_3_5_TABLE_NatSerializer019
