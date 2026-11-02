module

public import Structure.PSTR_LiveDispatchCode_127
public import Structure.PSTR_HD_ControlActual_149
public import Structure.PSTR_HD_HeadsCodeFits_127

/-! ONE fixed1514-op live program candidate, with the unchanged1371 query
body and genuine18/102/8/6 update dispatcher. Static slices are explicit;
actual complete execution is a separate obligation. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000
namespace PaperProofs.Structure.LaminarTree.PSTRLiveControllerCode

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def dispatch : List PackingOp := PSTRLiveDispatch.program 1494 1505 1514
def back : List PackingOp := PSTRCountControl.backBlock 1514
def prefix0 : List PackingOp := PSTRUniformQueryCode.program
def prefix1 : List PackingOp := prefix0 ++ dispatch
def prefix2 : List PackingOp := prefix1 ++ PSTRSelectedError.program
def prefix3 : List PackingOp := prefix2 ++ back
def prefix4 : List PackingOp := prefix3 ++ PSTRReplyControls.correctProgram
def prefix5 : List PackingOp := prefix4 ++ back
def prefix6 : List PackingOp := prefix5 ++ PSTRReplyControls.failProgram
def program : List PackingOp := prefix6 ++ back

theorem prefix0_length : prefix0.length = 1371 := PSTRUniformQueryCode.program_length
theorem prefix1_length : prefix1.length = 1389 := by
  rw [prefix1, List.length_append, prefix0_length, dispatch, PSTRLiveDispatch.program_length]
theorem prefix2_length : prefix2.length = 1491 := by
  rw [prefix2, List.length_append, prefix1_length, PSTRSelectedError.program_length]
theorem prefix3_length : prefix3.length = 1494 := by
  rw [prefix3, List.length_append, prefix2_length, back, PSTRCountControl.backBlock_length]
theorem prefix4_length : prefix4.length = 1502 := by
  rw [prefix4, List.length_append, prefix3_length, PSTRReplyControls.correct_length]
theorem prefix5_length : prefix5.length = 1505 := by
  rw [prefix5, List.length_append, prefix4_length, back, PSTRCountControl.backBlock_length]
theorem prefix6_length : prefix6.length = 1511 := by
  rw [prefix6, List.length_append, prefix5_length, PSTRReplyControls.fail_length]
theorem program_length : program.length = 1514 := by
  rw [program, List.length_append, prefix6_length, back, PSTRCountControl.backBlock_length]
theorem code_length : (packingCode program).length = 7575 := by
  rw [packingCode_length, program_length]

theorem body_contains : PSTRUniformQueryCode.Contains program := by
  have hp : program = PSTRUniformQueryCode.program ++
      (dispatch ++ PSTRSelectedError.program ++ back ++ PSTRReplyControls.correctProgram ++ back ++
        PSTRReplyControls.failProgram ++ back) := by
    simp only [program, prefix6, prefix5, prefix4, prefix3, prefix2, prefix1, prefix0, List.append_assoc]
  rw [hp]
  exact PSTRUniformQueryCode.append_contains _

theorem words16 : WordsFit 16 (packingCode program) := by
  have body : WordsFit 16 (packingCode prefix0) := PSTRUniformQueryCode.code_fit (by change 8192 < 2 ^ 16; decide)
  have disp : WordsFit 16 (packingCode dispatch) := PSTRLiveDispatch.code_fit _ _ _ (by decide)
    (by change 5 * 1494 < 2 ^ 16; decide) (by change 5 * 1505 < 2 ^ 16; decide) (by change 5 * 1514 < 2 ^ 16; decide)
  have selected : WordsFit 16 (packingCode PSTRSelectedError.program) := by unfold WordsFit Fits; decide
  have jump : WordsFit 16 (packingCode back) := by unfold WordsFit Fits; decide
  have correct : WordsFit 16 (packingCode PSTRReplyControls.correctProgram) := by unfold WordsFit Fits; decide
  have fail : WordsFit 16 (packingCode PSTRReplyControls.failProgram) := by unfold WordsFit Fits; decide
  have h1 := PSTRHeadsRuntime.heads_codeFit_append _ _ body disp
  have h2 := PSTRHeadsRuntime.heads_codeFit_append _ _ h1 selected
  have h3 := PSTRHeadsRuntime.heads_codeFit_append _ _ h2 jump
  have h4 := PSTRHeadsRuntime.heads_codeFit_append _ _ h3 correct
  have h5 := PSTRHeadsRuntime.heads_codeFit_append _ _ h4 jump
  have h6 := PSTRHeadsRuntime.heads_codeFit_append _ _ h5 fail
  exact PSTRHeadsRuntime.heads_codeFit_append _ _ h6 jump

theorem literal : ∀ value ∈ packingCode program, value < 65536 := words16

theorem program_words (N q : Nat) : WordsFit (indexWidth 32 N q) (packingCode program) := by
  have hb := PSTROriginalCountRoom.word_lower N q
  have hp : 2 ^ 32 ≤ 2 ^ indexWidth 32 N q := Nat.pow_le_pow_right (by decide) hb
  intro value hv
  exact (literal value hv).trans_le ((by decide : 65536 ≤ 2 ^ 32).trans hp)

theorem program_pc (N q : Nat) : Fits (indexWidth 32 N q) (5 * program.length) := by
  have hb := PSTROriginalCountRoom.word_lower N q
  have hp : 2 ^ 32 ≤ 2 ^ indexWidth 32 N q := Nat.pow_le_pow_right (by decide) hb
  rw [program_length]
  exact (by decide : 5 * 1514 < 2 ^ 32).trans_le hp

private theorem block_at (before block after : List PackingOp) (origin : Nat)
    (heq : program = before ++ block ++ after) (hlen : before.length = origin) :
    PSTROuterCountCode.BlockAt program origin block := by
  have bound : origin + block.length ≤ program.length := by
    rw [heq, List.length_append, List.length_append, hlen]
    omega
  refine ⟨bound, ?_⟩
  intro index hi
  have hg := congrArg (fun ops : List PackingOp => ops.getD (origin + index) (.base (.base (.constant .value 0)))) heq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp only [List.length_append, hlen]; omega)] at hg
  exact hg.trans (by simpa only [hlen] using PSTROuterCountCode.middle_get before block after index hi)

theorem dispatch_block : PSTROuterCountCode.BlockAt program 1371 dispatch := by
  apply block_at prefix0 dispatch (PSTRSelectedError.program ++ back ++ PSTRReplyControls.correctProgram ++ back ++ PSTRReplyControls.failProgram ++ back) 1371
  · simp only [program, prefix6, prefix5, prefix4, prefix3, prefix2, prefix1, List.append_assoc]
  · exact prefix0_length

theorem selected_block : PSTROuterCountCode.BlockAt program 1389 PSTRSelectedError.program := by
  apply block_at prefix1 PSTRSelectedError.program (back ++ PSTRReplyControls.correctProgram ++ back ++ PSTRReplyControls.failProgram ++ back) 1389
  · simp only [program, prefix6, prefix5, prefix4, prefix3, prefix2, List.append_assoc]
  · exact prefix1_length

theorem selected_return_block : PSTROuterCountCode.BlockAt program 1491 back := by
  apply block_at prefix2 back (PSTRReplyControls.correctProgram ++ back ++ PSTRReplyControls.failProgram ++ back) 1491
  · simp only [program, prefix6, prefix5, prefix4, prefix3, List.append_assoc]
  · exact prefix2_length

theorem correct_block : PSTROuterCountCode.BlockAt program 1494 PSTRReplyControls.correctProgram := by
  apply block_at prefix3 PSTRReplyControls.correctProgram (back ++ PSTRReplyControls.failProgram ++ back) 1494
  · simp only [program, prefix6, prefix5, prefix4, List.append_assoc]
  · exact prefix3_length

theorem correct_return_block : PSTROuterCountCode.BlockAt program 1502 back := by
  apply block_at prefix4 back (PSTRReplyControls.failProgram ++ back) 1502
  · simp only [program, prefix6, prefix5, List.append_assoc]
  · exact prefix4_length

theorem fail_block : PSTROuterCountCode.BlockAt program 1505 PSTRReplyControls.failProgram := by
  apply block_at prefix5 PSTRReplyControls.failProgram back 1505
  · simp only [program, prefix6, List.append_assoc]
  · exact prefix5_length

theorem fail_return_block : PSTROuterCountCode.BlockAt program 1511 back := by
  apply block_at prefix6 back [] 1511
  · simp only [program, List.append_nil]
  · exact prefix6_length

end PaperProofs.Structure.LaminarTree.PSTRLiveControllerCode
