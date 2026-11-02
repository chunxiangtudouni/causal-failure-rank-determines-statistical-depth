module

public import PaperProofs.Structure.PSTR_UniformBootstrapCode_105
public import PaperProofs.Structure.PSTR_CountControl_050
public import PaperProofs.Structure.PSTR_HD_ZeroLive_011
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeHeader_011a
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010b
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeRanks_008a
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ac
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeReply_016a

/-! ONE actual1371-op input-independent query body. Both branches have
genuine shared-exit jumps; the positive count63/header541/tail623 and
q0start1345/return1368 labels are literal code facts, not asserted shifts.
Execution correctness is provided by separate SAME-run producers. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000
namespace PaperProofs.Structure.LaminarTree.PSTRUniformQueryCode

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

def prefix0 : List PackingOp := []
def prefix1 : List PackingOp := prefix0 ++ (PSTRUniformBootstrapCode.program 1345)
def prefix2 : List PackingOp := prefix1 ++ (PSTROuterCountCode.programAt 63)
def prefix3 : List PackingOp := prefix2 ++ (PA17A19RuntimeHeader011.program)
def prefix4 : List PackingOp := prefix3 ++ (PA17A19RuntimeTests010.programAt 623)
def prefix5 : List PackingOp := prefix4 ++ (PA17A19RuntimeRanks008.programAt 978)
def prefix6 : List PackingOp := prefix5 ++ (PA17A19RuntimeSelect009.selectionCoreAt 1029)
def prefix7 : List PackingOp := prefix6 ++ (PA17A19RuntimeReply016.program)
def prefix8 : List PackingOp := prefix7 ++ (PSTRCountControl.backBlock 1371)
def prefix9 : List PackingOp := prefix8 ++ (PSTRZeroLive.program)
def program : List PackingOp := prefix9 ++ (PSTRCountControl.backBlock 1371)

theorem prefix0_length : prefix0.length = 0 := rfl
theorem prefix1_length : prefix1.length = 63 := by
  rw [prefix1, List.length_append, prefix0_length]
  have h : (PSTRUniformBootstrapCode.program 1345).length = 63 := rfl
  rw [h]
theorem prefix2_length : prefix2.length = 541 := by
  rw [prefix2, List.length_append, prefix1_length]
  have h : (PSTROuterCountCode.programAt 63).length = 478 := rfl
  rw [h]
theorem prefix3_length : prefix3.length = 623 := by
  rw [prefix3, List.length_append, prefix2_length]
  have h : (PA17A19RuntimeHeader011.program).length = 82 := rfl
  rw [h]
theorem prefix4_length : prefix4.length = 978 := by
  rw [prefix4, List.length_append, prefix3_length]
  have h : (PA17A19RuntimeTests010.programAt 623).length = 355 := rfl
  rw [h]
theorem prefix5_length : prefix5.length = 1029 := by
  rw [prefix5, List.length_append, prefix4_length]
  have h : (PA17A19RuntimeRanks008.programAt 978).length = 51 := rfl
  rw [h]
theorem prefix6_length : prefix6.length = 1310 := by
  rw [prefix6, List.length_append, prefix5_length]
  have h : (PA17A19RuntimeSelect009.selectionCoreAt 1029).length = 281 := rfl
  rw [h]
theorem prefix7_length : prefix7.length = 1342 := by
  rw [prefix7, List.length_append, prefix6_length]
  have h : (PA17A19RuntimeReply016.program).length = 32 := rfl
  rw [h]
theorem prefix8_length : prefix8.length = 1345 := by
  rw [prefix8, List.length_append, prefix7_length]
  have h : (PSTRCountControl.backBlock 1371).length = 3 := rfl
  rw [h]
theorem prefix9_length : prefix9.length = 1368 := by
  rw [prefix9, List.length_append, prefix8_length]
  have h : (PSTRZeroLive.program).length = 23 := rfl
  rw [h]
theorem program_length : program.length = 1371 := by
  rw [program, List.length_append, prefix9_length]
  rfl

theorem code_length : (packingCode program).length = 6860 := by
  rw [packingCode_length, program_length]

private theorem append_code_bound (left right : List PackingOp)
    (hl : ∀ value ∈ packingCode left, value < 8192)
    (hr : ∀ value ∈ packingCode right, value < 8192) :
    ∀ value ∈ packingCode (left ++ right), value < 8192 := by
  intro value hv
  simp only [packingCode, List.flatMap_append, List.mem_append] at hv
  rcases hv with (hv | hv) | hv
  · exact hl value (List.mem_append_left _ hv)
  · exact hr value (List.mem_append_left _ hv)
  · have hh : ∀ v ∈ haltWords.toArray.toList, v < 8192 := by decide
    exact hh value hv

private theorem literal_words_bound : ∀ value ∈ packingCode program, value < 8192 := by
  have h0 : ∀ value ∈ packingCode (PSTRUniformBootstrapCode.program 1345), value < 8192 := by decide
  have h1 : ∀ value ∈ packingCode (PSTROuterCountCode.programAt 63), value < 8192 := by decide
  have h2 : ∀ value ∈ packingCode (PA17A19RuntimeHeader011.program), value < 8192 := by decide
  have h3 : ∀ value ∈ packingCode (PA17A19RuntimeTests010.programAt 623), value < 8192 := by decide
  have h4 : ∀ value ∈ packingCode (PA17A19RuntimeRanks008.programAt 978), value < 8192 := by decide
  have h5 : ∀ value ∈ packingCode (PA17A19RuntimeSelect009.selectionCoreAt 1029), value < 8192 := by decide
  have h6 : ∀ value ∈ packingCode (PA17A19RuntimeReply016.program), value < 8192 := by decide
  have h7 : ∀ value ∈ packingCode (PSTRCountControl.backBlock 1371), value < 8192 := by decide
  have h8 : ∀ value ∈ packingCode (PSTRZeroLive.program), value < 8192 := by decide
  have h9 : ∀ value ∈ packingCode (PSTRCountControl.backBlock 1371), value < 8192 := by decide
  have p1 : ∀ value ∈ packingCode prefix1, value < 8192 := by
    simpa only [prefix1, prefix0, List.nil_append] using h0
  have p2 := append_code_bound prefix1 (PSTROuterCountCode.programAt 63) p1 h1
  have p3 := append_code_bound prefix2 (PA17A19RuntimeHeader011.program) p2 h2
  have p4 := append_code_bound prefix3 (PA17A19RuntimeTests010.programAt 623) p3 h3
  have p5 := append_code_bound prefix4 (PA17A19RuntimeRanks008.programAt 978) p4 h4
  have p6 := append_code_bound prefix5 (PA17A19RuntimeSelect009.selectionCoreAt 1029) p5 h5
  have p7 := append_code_bound prefix6 (PA17A19RuntimeReply016.program) p6 h6
  have p8 := append_code_bound prefix7 (PSTRCountControl.backBlock 1371) p7 h7
  have p9 := append_code_bound prefix8 (PSTRZeroLive.program) p8 h8
  exact append_code_bound prefix9 (PSTRCountControl.backBlock 1371) p9 h9

theorem code_fit {bits : Nat} (room : Fits bits 8192) : WordsFit bits (packingCode program) := by
  intro value hv
  exact (literal_words_bound value hv).trans room

theorem pc_fit {bits : Nat} (room : Fits bits 8192) : Fits bits (5 * program.length) := by
  rw [program_length]
  exact (by decide : 5 * 1371 < 8192).trans room

private theorem block_at (before block after : List PackingOp) (origin : Nat)
    (heq : program = before ++ block ++ after) (hlen : before.length = origin) :
    PSTROuterCountCode.BlockAt program origin block := by
  have bound : origin + block.length ≤ program.length := by
    rw [heq, List.length_append, List.length_append, hlen]
    omega
  refine ⟨bound, ?_⟩
  intro i hi
  have hg := congrArg (fun ops : List PackingOp => ops.getD (origin + i) (.base (.base (.constant .value 0)))) heq
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by simp only [List.length_append, hlen]; omega)] at hg
  exact hg.trans (by simpa only [hlen] using PSTROuterCountCode.middle_get before block after i hi)

theorem bootstrap_block : PSTROuterCountCode.BlockAt program 0 (PSTRUniformBootstrapCode.program 1345) := by
  apply block_at prefix0 (PSTRUniformBootstrapCode.program 1345) ((PSTROuterCountCode.programAt 63) ++ (PA17A19RuntimeHeader011.program) ++ (PA17A19RuntimeTests010.programAt 623) ++ (PA17A19RuntimeRanks008.programAt 978) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1029) ++ (PA17A19RuntimeReply016.program) ++ (PSTRCountControl.backBlock 1371) ++ (PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 0
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix0_length

theorem counts_block : PSTROuterCountCode.BlockAt program 63 (PSTROuterCountCode.programAt 63) := by
  apply block_at prefix1 (PSTROuterCountCode.programAt 63) ((PA17A19RuntimeHeader011.program) ++ (PA17A19RuntimeTests010.programAt 623) ++ (PA17A19RuntimeRanks008.programAt 978) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1029) ++ (PA17A19RuntimeReply016.program) ++ (PSTRCountControl.backBlock 1371) ++ (PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 63
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix1_length

theorem header_block : PSTROuterCountCode.BlockAt program 541 (PA17A19RuntimeHeader011.program) := by
  apply block_at prefix2 (PA17A19RuntimeHeader011.program) ((PA17A19RuntimeTests010.programAt 623) ++ (PA17A19RuntimeRanks008.programAt 978) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1029) ++ (PA17A19RuntimeReply016.program) ++ (PSTRCountControl.backBlock 1371) ++ (PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 541
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix2_length

theorem tests_block : PSTROuterCountCode.BlockAt program 623 (PA17A19RuntimeTests010.programAt 623) := by
  apply block_at prefix3 (PA17A19RuntimeTests010.programAt 623) ((PA17A19RuntimeRanks008.programAt 978) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1029) ++ (PA17A19RuntimeReply016.program) ++ (PSTRCountControl.backBlock 1371) ++ (PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 623
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix3_length

theorem ranks_block : PSTROuterCountCode.BlockAt program 978 (PA17A19RuntimeRanks008.programAt 978) := by
  apply block_at prefix4 (PA17A19RuntimeRanks008.programAt 978) ((PA17A19RuntimeSelect009.selectionCoreAt 1029) ++ (PA17A19RuntimeReply016.program) ++ (PSTRCountControl.backBlock 1371) ++ (PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 978
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix4_length

theorem selector_block : PSTROuterCountCode.BlockAt program 1029 (PA17A19RuntimeSelect009.selectionCoreAt 1029) := by
  apply block_at prefix5 (PA17A19RuntimeSelect009.selectionCoreAt 1029) ((PA17A19RuntimeReply016.program) ++ (PSTRCountControl.backBlock 1371) ++ (PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 1029
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix5_length

theorem reply_block : PSTROuterCountCode.BlockAt program 1310 (PA17A19RuntimeReply016.program) := by
  apply block_at prefix6 (PA17A19RuntimeReply016.program) ((PSTRCountControl.backBlock 1371) ++ (PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 1310
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix6_length

theorem positive_return_block : PSTROuterCountCode.BlockAt program 1342 (PSTRCountControl.backBlock 1371) := by
  apply block_at prefix7 (PSTRCountControl.backBlock 1371) ((PSTRZeroLive.program) ++ (PSTRCountControl.backBlock 1371)) 1342
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix7_length

theorem zero_block : PSTROuterCountCode.BlockAt program 1345 (PSTRZeroLive.program) := by
  apply block_at prefix8 (PSTRZeroLive.program) ((PSTRCountControl.backBlock 1371)) 1345
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append]
  · exact prefix8_length

theorem zero_return_block : PSTROuterCountCode.BlockAt program 1368 (PSTRCountControl.backBlock 1371) := by
  apply block_at prefix9 (PSTRCountControl.backBlock 1371) ([]) 1368
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, prefix7, prefix8, prefix9, List.append_assoc, List.nil_append, List.append_nil]
  · exact prefix9_length

structure Contains (whole : List PackingOp) : Prop where
  bound : program.length ≤ whole.length
  code : ∀ i (hi : i < program.length), whole[i]'(by omega) = program[i]

theorem self_contains : Contains program := ⟨Nat.le_refl _, fun _ _ => rfl⟩

theorem append_contains (tail : List PackingOp) : Contains (program ++ tail) := by
  refine ⟨by rw [List.length_append]; omega, ?_⟩
  intro i hi
  exact List.getElem_append_left hi

theorem block_in (whole : List PackingOp) (contains : Contains whole) (origin : Nat) (block : List PackingOp)
    (localBlock : PSTROuterCountCode.BlockAt program origin block) : PSTROuterCountCode.BlockAt whole origin block := by
  refine ⟨localBlock.bound.trans contains.bound, ?_⟩
  intro i hi
  exact (contains.code (origin + i) (by have h := localBlock.bound; omega)).trans (localBlock.code i hi)

theorem bootstrap_in (whole : List PackingOp) (contains : Contains whole) :
    PSTRUniformBootstrapCode.Contains whole 1345 := by
  have h := block_in whole contains 0 _ bootstrap_block
  refine ⟨by simpa only [Nat.zero_add] using h.bound, ?_⟩
  intro i hi
  simpa only [Nat.zero_add] using h.code i hi

theorem counts_in (whole : List PackingOp) (contains : Contains whole) : PSTROuterCountCode.Contains whole 63 :=
  block_in whole contains 63 _ counts_block

theorem zero_in (whole : List PackingOp) (contains : Contains whole) :
    PSTROuterCountCode.BlockAt whole 1345 PSTRZeroLive.program := block_in whole contains 1345 _ zero_block

theorem zero_return_in (whole : List PackingOp) (contains : Contains whole) :
    PSTROuterCountCode.BlockAt whole (1345 + 23) (PSTRCountControl.backBlock 1371) :=
  block_in whole contains 1368 _ zero_return_block

theorem positive_return_in (whole : List PackingOp) (contains : Contains whole) :
    PSTROuterCountCode.BlockAt whole 1342 (PSTRCountControl.backBlock 1371) :=
  block_in whole contains 1342 _ positive_return_block

end PaperProofs.Structure.LaminarTree.PSTRUniformQueryCode
