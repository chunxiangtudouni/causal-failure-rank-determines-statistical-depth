module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeEntry_020c
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_Semantics_019e
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ba
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeReply_016c

/-! One fixed positive-query instruction array, with no input-dependent
code parameters. Its real constituent embeddings are proved below.
Operational correctness is supplied by the separate same-run entry/tail proofs. -/

@[expose] public section
set_option maxRecDepth 24000
set_option maxHeartbeats 2400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeProgram027

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def prefix0 : List PackingOp := []
def prefix1 : List PackingOp := prefix0 ++ (PSTRCountBootstrapCode.program)
def prefix2 : List PackingOp := prefix1 ++ (PSTROuterCountCode.programAt 61)
def prefix3 : List PackingOp := prefix2 ++ (PA17A19RuntimeHeader011.program)
def prefix4 : List PackingOp := prefix3 ++ (PA17A19RuntimeTests010.programAt 621)
def prefix5 : List PackingOp := prefix4 ++ (PA17A19RuntimeRanks008.programAt 976)
def prefix6 : List PackingOp := prefix5 ++ (PA17A19RuntimeSelect009.selectionCoreAt 1027)

def program : List PackingOp := prefix6 ++ (PA17A19RuntimeReply016.program)

theorem prefix0_length : prefix0.length = 0 := by
  rfl

theorem prefix1_length : prefix1.length = 61 := by
  rw [prefix1, List.length_append, prefix0_length]
  have h : (PSTRCountBootstrapCode.program).length = 61 := by rfl
  rw [h]

theorem prefix2_length : prefix2.length = 539 := by
  rw [prefix2, List.length_append, prefix1_length]
  have h : (PSTROuterCountCode.programAt 61).length = 478 := by rfl
  rw [h]

theorem prefix3_length : prefix3.length = 621 := by
  rw [prefix3, List.length_append, prefix2_length]
  have h : (PA17A19RuntimeHeader011.program).length = 82 := by rfl
  rw [h]

theorem prefix4_length : prefix4.length = 976 := by
  rw [prefix4, List.length_append, prefix3_length]
  have h : (PA17A19RuntimeTests010.programAt 621).length = 355 := by rfl
  rw [h]

theorem prefix5_length : prefix5.length = 1027 := by
  rw [prefix5, List.length_append, prefix4_length]
  have h : (PA17A19RuntimeRanks008.programAt 976).length = 51 := by rfl
  rw [h]

theorem prefix6_length : prefix6.length = 1308 := by
  rw [prefix6, List.length_append, prefix5_length]
  have h : (PA17A19RuntimeSelect009.selectionCoreAt 1027).length = 281 := by rfl
  rw [h]

theorem program_length : program.length = 1340 := by
  rw [program, List.length_append, prefix6_length]
  rfl

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
  have h0 : ∀ value ∈ packingCode PSTRCountBootstrapCode.program, value < 8192 := by decide
  have h1 : ∀ value ∈ packingCode (PSTROuterCountCode.programAt 61), value < 8192 := by decide
  have h2 : ∀ value ∈ packingCode PA17A19RuntimeHeader011.program, value < 8192 := by decide
  have h3 : ∀ value ∈ packingCode (PA17A19RuntimeTests010.programAt 621), value < 8192 := by decide
  have h4 : ∀ value ∈ packingCode (PA17A19RuntimeRanks008.programAt 976), value < 8192 := by decide
  have h5 : ∀ value ∈ packingCode (PA17A19RuntimeSelect009.selectionCoreAt 1027), value < 8192 := by decide
  have h6 : ∀ value ∈ packingCode PA17A19RuntimeReply016.program, value < 8192 := by decide
  have p1 : ∀ value ∈ packingCode prefix1, value < 8192 := by
    simpa only [prefix1, prefix0, List.nil_append] using h0
  have p2 := append_code_bound prefix1 (PSTROuterCountCode.programAt 61) p1 h1
  have p3 := append_code_bound prefix2 PA17A19RuntimeHeader011.program p2 h2
  have p4 := append_code_bound prefix3 (PA17A19RuntimeTests010.programAt 621) p3 h3
  have p5 := append_code_bound prefix4 (PA17A19RuntimeRanks008.programAt 976) p4 h4
  have p6 := append_code_bound prefix5 (PA17A19RuntimeSelect009.selectionCoreAt 1027) p5 h5
  exact append_code_bound prefix6 PA17A19RuntimeReply016.program p6 h6

theorem code_fit {bits : Nat} (room : Fits bits 8192) : WordsFit bits (packingCode program) := by
  intro value hv
  exact (literal_words_bound value hv).trans room

theorem pc_fit {bits : Nat} (room : Fits bits 8192) : Fits bits (5 * program.length) := by
  rw [program_length]
  exact (by decide : 5 * 1340 < 8192).trans room

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

theorem bootstrap_block : PSTROuterCountCode.BlockAt program 0 (PSTRCountBootstrapCode.program) := by
  apply block_at prefix0 (PSTRCountBootstrapCode.program) ((PSTROuterCountCode.programAt 61) ++ (PA17A19RuntimeHeader011.program) ++ (PA17A19RuntimeTests010.programAt 621) ++ (PA17A19RuntimeRanks008.programAt 976) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1027) ++ (PA17A19RuntimeReply016.program)) 0
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, List.append_assoc, List.nil_append]
  · exact prefix0_length

theorem counts_block : PSTROuterCountCode.BlockAt program 61 (PSTROuterCountCode.programAt 61) := by
  apply block_at prefix1 (PSTROuterCountCode.programAt 61) ((PA17A19RuntimeHeader011.program) ++ (PA17A19RuntimeTests010.programAt 621) ++ (PA17A19RuntimeRanks008.programAt 976) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1027) ++ (PA17A19RuntimeReply016.program)) 61
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, List.append_assoc, List.nil_append]
  · exact prefix1_length

theorem header_block : PSTROuterCountCode.BlockAt program 539 (PA17A19RuntimeHeader011.program) := by
  apply block_at prefix2 (PA17A19RuntimeHeader011.program) ((PA17A19RuntimeTests010.programAt 621) ++ (PA17A19RuntimeRanks008.programAt 976) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1027) ++ (PA17A19RuntimeReply016.program)) 539
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, List.append_assoc, List.nil_append]
  · exact prefix2_length

theorem tests_block : PSTROuterCountCode.BlockAt program 621 (PA17A19RuntimeTests010.programAt 621) := by
  apply block_at prefix3 (PA17A19RuntimeTests010.programAt 621) ((PA17A19RuntimeRanks008.programAt 976) ++ (PA17A19RuntimeSelect009.selectionCoreAt 1027) ++ (PA17A19RuntimeReply016.program)) 621
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, List.append_assoc, List.nil_append]
  · exact prefix3_length

theorem ranks_block : PSTROuterCountCode.BlockAt program 976 (PA17A19RuntimeRanks008.programAt 976) := by
  apply block_at prefix4 (PA17A19RuntimeRanks008.programAt 976) ((PA17A19RuntimeSelect009.selectionCoreAt 1027) ++ (PA17A19RuntimeReply016.program)) 976
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, List.append_assoc, List.nil_append]
  · exact prefix4_length

theorem selector_block : PSTROuterCountCode.BlockAt program 1027 (PA17A19RuntimeSelect009.selectionCoreAt 1027) := by
  apply block_at prefix5 (PA17A19RuntimeSelect009.selectionCoreAt 1027) ((PA17A19RuntimeReply016.program)) 1027
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, List.append_assoc, List.nil_append]
  · exact prefix5_length

theorem footer_block : PSTROuterCountCode.BlockAt program 1308 (PA17A19RuntimeReply016.program) := by
  apply block_at prefix6 (PA17A19RuntimeReply016.program) ([]) 1308
  · simp only [program, prefix0, prefix1, prefix2, prefix3, prefix4, prefix5, prefix6, List.append_assoc, List.nil_append, List.append_nil]
  · exact prefix6_length

theorem contains_bootstrap : PSTRBootstrapSlices.Contains program := by
  refine ⟨by rw [program_length]; decide, ?_⟩
  intro i hi
  simpa only [Nat.zero_add] using bootstrap_block.code i hi

theorem contains_counts : PSTROuterCountCode.Contains program 61 := counts_block

theorem embedded_header {bits : Nat} (room : Fits bits 8192) :
    PA17A19RuntimeHeader011.Embedded bits 539 program :=
  ⟨header_block.bound, header_block.code, code_fit room, pc_fit room⟩

theorem embedded_tests {bits : Nat} (room : Fits bits 8192) :
    PA17A19RuntimeTests010.Embedded bits 621 program :=
  ⟨tests_block.bound, tests_block.code, code_fit room, pc_fit room⟩

theorem embedded_ranks {bits : Nat} (room : Fits bits 8192) :
    PA17A19RuntimeRanks008.Embedded bits 976 program :=
  ⟨ranks_block.bound, ranks_block.code, code_fit room, pc_fit room⟩

theorem embedded_selector {bits : Nat} (room : Fits bits 8192) :
    PA17A19RuntimeSelect009.CoreEmbedded bits 1027 program :=
  ⟨selector_block.bound, selector_block.code, code_fit room, pc_fit room⟩

theorem embedded_footer {bits : Nat} (room : Fits bits 8192) :
    PA17A19RuntimeReply016.Embedded bits 1308 program :=
  ⟨footer_block.bound, footer_block.code, code_fit room, pc_fit room⟩

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeProgram027
