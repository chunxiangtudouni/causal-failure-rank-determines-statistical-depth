module

public import PaperProofs.Structure.RawCandidateTreePrefix
public import PaperProofs.Structure.RawCandidateSerializedChildrenRAM
public import PaperProofs.Structure.RawTreeOutputFinalizeRAM
public import PaperProofs.Structure.PackingWordBounds

/-! Exact code-only bounds for the single complete raw constructor.
The instruction stream and all its immediates precede N/q/full.  These
lemmas do not assert bounds on any runtime register or heap access. -/

@[expose] public section

set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.RawTreePreprocessingCodeBounds

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims PackingMachine

/-- Fixed body; the actual encoded HALT is appended by packingCode. -/
def program : List PackingOp :=
  RawCandidateTreePrefix.program
    (RawCandidateSerializedChildrenRAM.programAt 1649 ++ RawTreeOutputFinalizeRAM.program)

theorem program_length : program.length = 2089 := by
  rw [program, ← RawCandidateTreePrefix.serializedProgram_eq,
    List.length_append, RawCandidateTreePrefix.serializedFront_length,
    RawCandidateTreePrefix.inputStart_eq, List.length_append,
    RawCandidateSerializedChildrenRAM.programAt_length, RawTreeOutputFinalizeRAM.program_length]

theorem bodyWords_length : (PackingMachine.bodyWords program).length = 10445 := by
  rw [PackingMachine.bodyWords_length, program_length]

/-- Five words per instruction, including five words for the real HALT. -/
theorem code_length : (packingCode program).length = 10450 := by
  rw [packingCode_length, program_length]

theorem halt_pc : 5 * program.length = 10445 := by rw [program_length]

private theorem instruction_word_certificate :
    program.all (fun op => op.encode.toArray.toList.all (fun word => decide (word ≤ 10445))) = true := by decide

/-- The maximum word is the dispatcher's actual terminal-PC immediate. -/
theorem code_word_le : ∀ value ∈ packingCode program, value ≤ 10445 := by
  intro value hv
  rcases List.mem_append.mp hv with hv | hv
  · rcases List.mem_flatMap.mp hv with ⟨op, hop, hword⟩
    have h := List.all_eq_true.mp instruction_word_certificate op hop
    exact of_decide_eq_true (List.all_eq_true.mp h value hword)
  · have hh : ∀ word ∈ haltWords.toArray.toList, word ≤ 10445 := by decide
    exact hh value hv

theorem terminal_pc_mem_code : 10445 ∈ packingCode program := by decide

theorem op_word_le (op : PackingOp) (hop : op ∈ program) :
    ∀ value ∈ op.encode.toArray.toList, value ≤ 10445 := by
  intro value hv
  apply code_word_le value
  apply List.mem_append_left
  exact List.mem_flatMap.mpr ⟨op, hop, hv⟩

/-- This scalar fact holds even before restricting to the positive-q
branch: the original logarithmic width has at least sixteen bits. -/
theorem constant_fits (N q value : Nat) (hv : value ≤ 10450) : Fits (indexWidth 16 N q) value := by
  apply fits_indexWidth_of_lt_power
  have hpower : 2 ^ 16 ≤ (N + q + 2) ^ 16 := Nat.pow_le_pow_left (by omega) 16
  omega

theorem wordsFit (N q : Nat) : WordsFit (indexWidth 16 N q) (packingCode program) := by
  intro value hv
  exact constant_fits N q value ((code_word_le value hv).trans (by omega))

theorem code_length_fits (N q : Nat) : Fits (indexWidth 16 N q) (packingCode program).length := by
  rw [code_length]
  exact constant_fits N q 10450 le_rfl

theorem instruction_count_fits (N q : Nat) : Fits (indexWidth 16 N q) program.length := by
  rw [program_length]
  exact constant_fits N q 2089 (by omega)

theorem halt_pc_fits (N q : Nat) : Fits (indexWidth 16 N q) (5 * program.length) := by
  rw [halt_pc]
  exact constant_fits N q 10445 (by omega)

/-- This is an indexed-code fact, not a claim that every runtime PC
satisfies its hypothesis. Runtime control safety remains a separate proof. -/
theorem fetch_window (index : Nat) (hi : index ≤ program.length) :
    5 * index ≤ 10445 ∧ 5 * index + 4 < (packingCode program).length := by
  rw [program_length] at hi
  rw [code_length]
  omega

theorem fetch_address_fits (N q index position : Nat) (hi : index ≤ program.length) (hp : position < 5) :
    Fits (indexWidth 16 N q) (5 * index + position) := by
  apply constant_fits
  have h := fetch_window index hi
  rw [code_length] at h
  omega

/-- Every encoded word of each actual body instruction fits. This includes
all constant operands, opcode tags, region tags and register numbers. -/
theorem instruction_wordsFit (N q : Nat) (op : PackingOp) (hop : op ∈ program) :
    WordsFit (indexWidth 16 N q) op.encode.toArray.toList := by
  intro value hv
  exact constant_fits N q value ((op_word_le op hop value hv).trans (by omega))

theorem physical_code_length (N q : Nat) :
    ((packingCode program).map (BitVec.ofNat (indexWidth 16 N q))).length = 10450 := by
  rw [List.length_map, code_length]

theorem physical_code_getD (N q index : Nat) :
    (((packingCode program).map (BitVec.ofNat (indexWidth 16 N q))).getD index
      (BitVec.ofNat (indexWidth 16 N q) 0)).toNat = (packingCode program).getD index 0 :=
  getD_map_ofNat _ _ index (wordsFit N q)

theorem physical_fetch (N q pc : Nat) :
    physicalFetch (indexWidth 16 N q) (packingCode program) pc = natFetch program pc :=
  physicalFetch_eq _ _ pc (wordsFit N q)

theorem physical_fetch_body (N q index : Nat) (hi : index < program.length) :
    physicalFetch (indexWidth 16 N q) (packingCode program) (5 * index) = (program[index]'hi).encode := by
  rw [physical_fetch, natFetch_body program index hi]

theorem physical_decode_body (N q index : Nat) (hi : index < program.length) :
    PackingOp.decode (physicalFetch (indexWidth 16 N q) (packingCode program) (5 * index)) =
      some (program[index]'hi) := by
  rw [physical_fetch_body N q index hi, decode_encode]

theorem physical_fetch_halt (N q : Nat) :
    physicalFetch (indexWidth 16 N q) (packingCode program) 10445 = haltWords := by
  rw [← halt_pc, physical_fetch, natFetch_halt]

theorem physical_decode_halt (N q : Nat) :
    PackingOp.decode (physicalFetch (indexWidth 16 N q) (packingCode program) 10445) = none := by
  rw [physical_fetch_halt, decode_halt]

end PaperProofs.Structure.LaminarTree.RawTreePreprocessingCodeBounds
