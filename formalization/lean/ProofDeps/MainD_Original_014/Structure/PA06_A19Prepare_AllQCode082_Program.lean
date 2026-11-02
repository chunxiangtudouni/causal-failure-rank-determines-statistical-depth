module

public import Structure.PA06_A19Prepare_RawActive076_Layout
public import Structure.PA06_A19Prepare_EarlyGate079_Program
public import Structure.PA06_A19Prepare_ZeroHeader080_Program
public import Structure.PA06_A19Prepare_CodeFit052_Program

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED layout of ONE fixed all-q program. The old raw dispatcher
is generated with the complete skip/zero-handler tail already present.
Only the first ten instructions are patched, at unchanged offsets. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM

def bodyEnd : Nat := PA06A19PrepareRawActive076.builderEnd + 691
def handlerStart : Nat := bodyEnd + 3
def finalEnd : Nat := handlerStart + 60
def skip : List PackingOp := jumpTo finalEnd
def zeroBody : List PackingOp := PA06A19PrepareZeroHeader080.programAt handlerStart
def right : List PackingOp := skip ++ zeroBody
def oldP : List PackingOp := PA06A19PrepareRawActive076.program right
def program : List PackingOp := PA06A19PrepareEarlyGate079.program (5 * handlerStart) oldP

def oldPrefix : List PackingOp := PA06A19PrepareRawActive076.front right
def patchedPrefix : List PackingOp :=
  PA06A19PrepareEarlyGate079.program (5 * handlerStart) oldPrefix
def builderFront : List PackingOp := patchedPrefix ++ PA06A19PrepareCodeFit052.builderProgram
def positiveBody : List PackingOp := builderFront ++ PA06A19PrepareCodeFit052.afterBuilder
def handlerLeft : List PackingOp := positiveBody ++ skip

theorem skip_length : skip.length = 3 := rfl
theorem zeroBody_length : zeroBody.length = 60 :=
  PA06A19PrepareZeroHeader080.programAt_length handlerStart

theorem right_length : right.length = 63 := by
  rw [right, List.length_append, skip_length, zeroBody_length]

theorem oldPrefix_length : oldPrefix.length = 1639 :=
  PA06A19PrepareRawActive076.front_length right

theorem patchedPrefix_length : patchedPrefix.length = 1639 := by
  rw [patchedPrefix, PA06A19PrepareEarlyGate079.program_length]
  · exact oldPrefix_length
  · rw [oldPrefix_length]
    decide

theorem builderFront_length : builderFront.length = PA06A19PrepareRawActive076.builderEnd := by
  rw [builderFront, List.length_append, patchedPrefix_length]
  simp only [PA06A19PrepareRawActive076.builderEnd, PA06A19PrepareCodeFit052.builderProgram]

theorem positiveBody_length : positiveBody.length = bodyEnd := by
  rw [positiveBody, List.length_append, builderFront_length,
    PA06A19PrepareCodeFit052.afterBuilder_length]
  rfl

theorem handlerLeft_length : handlerLeft.length = handlerStart := by
  rw [handlerLeft, List.length_append, positiveBody_length, skip_length]
  rfl

theorem oldP_length : oldP.length = finalEnd := by
  rw [oldP, PA06A19PrepareRawActive076.program_length, right_length]
  unfold finalEnd handlerStart bodyEnd
  omega

theorem program_length : program.length = finalEnd := by
  rw [program, PA06A19PrepareEarlyGate079.program_length]
  · exact oldP_length
  · rw [oldP_length]
    unfold finalEnd handlerStart bodyEnd
    omega

theorem bodyTail_eq : PA06A19PrepareRawActive076.bodyTail right =
    PA06A19PrepareCodeFit052.afterBuilder ++ right := by
  simp only [PA06A19PrepareRawActive076.bodyTail,
    PA06A19PrepareActiveSuffix076.tail, PA06A19PrepareActiveSuffix076.metadataRight,
    PA06A19PrepareCodeFit052.afterBuilder, PA06A19PrepareCodeFit052.metadataSegment,
    PA06A19PrepareCodeFit052.usedSegment, PA06A19PrepareCodeFit052.finalSegment,
    PA06A19PrepareRawActive076.builderEnd, PA06A19PrepareCodeFit052.builderEnd,
    PA06A19PrepareCodeFit052.builderProgram, List.append_assoc]

theorem oldP_layout :
    oldPrefix ++ PA06A19PrepareCodeFit052.builderProgram ++
      PA06A19PrepareCodeFit052.afterBuilder ++ right = oldP := by
  have layout := PA06A19PrepareRawActive076.builder_layout right
  rw [PA06A19PrepareRawActive076.front_length, bodyTail_eq] at layout
  simpa only [oldPrefix, PA06A19PrepareCodeFit052.builderProgram, oldP,
    List.append_assoc] using layout

theorem patch_append (handlerPC : Nat) (left tail : List PackingOp)
    (room : 10 ≤ left.length) :
    PA06A19PrepareEarlyGate079.program handlerPC (left ++ tail) =
      PA06A19PrepareEarlyGate079.program handlerPC left ++ tail := by
  unfold PA06A19PrepareEarlyGate079.program
  rw [List.drop_append_of_le_length room, List.append_assoc]

theorem program_layout :
    patchedPrefix ++ PA06A19PrepareCodeFit052.builderProgram ++
      PA06A19PrepareCodeFit052.afterBuilder ++ right = program := by
  have oldLayout : oldP = oldPrefix ++ (PA06A19PrepareCodeFit052.builderProgram ++
      PA06A19PrepareCodeFit052.afterBuilder ++ right) := by
    simpa only [List.append_assoc] using oldP_layout.symm
  have room : 10 ≤ oldPrefix.length := by rw [oldPrefix_length]; decide
  rw [program, oldLayout, patch_append _ _ _ room]
  simp only [patchedPrefix, List.append_assoc]

theorem positive_layout : positiveBody ++ right = program := program_layout

/-- The containing builder uses the PATCHED prefix, never the old prefix. -/
theorem builder_layout :
    patchedPrefix ++ PSTRBuildLower.CounterInit.builderCode patchedPrefix.length ++
      PA06A19PrepareRawActive076.bodyTail right = program := by
  rw [patchedPrefix_length, bodyTail_eq]
  simpa only [PA06A19PrepareCodeFit052.builderProgram, List.append_assoc] using program_layout

theorem suffix_layout :
    PA06A19PrepareActiveSuffix076.program builderFront right = program := by
  unfold PA06A19PrepareActiveSuffix076.program
  rw [builderFront_length]
  change builderFront ++ PA06A19PrepareRawActive076.bodyTail right = program
  rw [bodyTail_eq]
  simpa only [positiveBody, List.append_assoc] using positive_layout

theorem skip_layout : positiveBody ++ jumpTo finalEnd ++ zeroBody = program := by
  simpa only [right, skip, List.append_assoc] using positive_layout

theorem handler_layout :
    handlerLeft ++ PA06A19PrepareZeroHeader080.programAt handlerStart = program := skip_layout

theorem handler_program_layout :
    handlerLeft ++ PA06A19PrepareZeroHeader080.programAt handlerLeft.length ++ [] = program := by
  rw [handlerLeft_length, List.append_nil]
  exact handler_layout

theorem positive_prefix : program.take bodyEnd = positiveBody := by
  rw [← positive_layout, ← positiveBody_length]
  exact List.take_append_length

theorem skip_slice : (program.drop bodyEnd).take 3 = skip := by
  rw [← positive_layout, ← positiveBody_length, List.drop_append_length]
  change (skip ++ zeroBody).take 3 = skip
  rw [← skip_length]
  exact List.take_append_length

theorem handler_slice : program.drop handlerStart = zeroBody := by
  have dropped := List.drop_append_length (l₁ := handlerLeft) (l₂ := zeroBody)
  have layout : handlerLeft ++ zeroBody = program := handler_layout
  rw [layout, handlerLeft_length] at dropped
  exact dropped

theorem patched_prefix_slice : program.take 1639 = patchedPrefix := by
  have room : 1639 ≤ patchedPrefix.length := by rw [patchedPrefix_length]
  rw [← program_layout, List.append_assoc, List.append_assoc,
    List.take_append_of_le_length room]
  simpa only [patchedPrefix_length] using (List.take_length (l := patchedPrefix))

/-- The old constructor is recovered from this exact WHOLE program.
Its dispatcher consequently names the final HALT after the zero handler. -/
theorem oldP_dispatcher : oldP = dispatcherProgram (oldP.drop 128) := rfl

theorem oldP_checker : oldP = checker ++ oldP.drop 126 := by
  have hprefix : oldP.take 126 = checker := rfl
  calc
    oldP = oldP.take 126 ++ oldP.drop 126 := (List.take_append_drop 126 oldP).symm
    _ = checker ++ oldP.drop 126 := by rw [hprefix]

private theorem dispatcher_slice_of_constructor (constructor : List PackingOp) :
    ((dispatcherProgram constructor).drop checker.length).take 2 =
      [.base (.base (.constant .index (5 * (dispatcherProgram constructor).length))),
        .jumpIfZero .value .index] := by
  calc
    _ = (dispatcherGate constructor.length ++ constructor).take 2 := by
      rw [dispatcherProgram, List.append_assoc, List.drop_append_length]
    _ = dispatcherGate constructor.length := by
      simpa only [dispatcherGate_length] using
        (List.take_append_length (l₁ := dispatcherGate constructor.length) (l₂ := constructor))
    _ = _ := by simp only [dispatcherGate, dispatcherProgram_length]

theorem oldP_dispatcher_slice : (oldP.drop 126).take 2 =
    [.base (.base (.constant .index (5 * oldP.length))), .jumpIfZero .value .index] := by
  simpa only [checker_length, ← oldP_dispatcher] using
    (dispatcher_slice_of_constructor (oldP.drop 128))

theorem program_drop10 : program.drop 10 = oldP.drop 10 :=
  PA06A19PrepareEarlyGate079.program_drop10 _ _

theorem program_drop_after (cut : Nat) (bound : 10 ≤ cut) :
    program.drop cut = oldP.drop cut := by
  have kept := congrArg (List.drop (cut - 10)) program_drop10
  simp only [List.drop_drop, Nat.add_sub_of_le bound] at kept
  exact kept

theorem program_drop126 : program.drop 126 = oldP.drop 126 := program_drop_after 126 (by decide)

theorem program_drop1639 : program.drop 1639 = oldP.drop 1639 := program_drop_after 1639 (by decide)

theorem dispatcher_slice : (program.drop 126).take 2 =
    [.base (.base (.constant .index (5 * finalEnd))), .jumpIfZero .value .index] := by
  rw [program_drop126, oldP_dispatcher_slice, oldP_length]

theorem program_code_length : (packingCode program).length = 5 * finalEnd + 5 := by
  rw [packingCode_length, program_length]

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQCode082
