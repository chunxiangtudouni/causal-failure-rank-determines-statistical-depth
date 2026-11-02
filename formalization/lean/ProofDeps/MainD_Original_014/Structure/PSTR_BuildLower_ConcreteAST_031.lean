module

public import Structure.PSTR_BuildLower_NodeFramed_027
public import Structure.PSTR_BuildLower_ConcreteHeap_028
public import Structure.PSTR_BuildLower_InternalInput_030
public import Structure.PSTR_BuildLower_ROMUse_020

/-! ONE concrete fixed fullBuild code. All ports contain actual instructions:
raw stage input, copied-cache/raw node query, parent/degree bank, real A06
packed backend, and ordinary rebasing. Complete AST simulation remains separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PA17ProgramTemplates041
variable {bits : Nat}

def inputHead (nodePC : Nat) (pointer : Register) : List PackingOp :=
  relativeRead (registerOffset pointer) .old ++ relativeRead 0 .total ++ relativeRead 1 .value ++
    [.arithmetic .multiply .total .total .value, .base (.base (.constant .fresh 3)),
     .base (.base (.add .total .total .fresh)), .base (.subtract .flag .total .old),
     .base (.base (.constant .index nodePC)), .jumpIfZero .flag .index]

def inputCode (start : Nat) (pointer : Register) : List PackingOp :=
  inputHead (5 * (start + 24)) pointer ++ StageInput.code pointer ++
    forwardJump (5 * (start + 87)) ++ NodeInput.nodeBitCode (start + 24) pointer

theorem inputHead_length (nodePC : Nat) (pointer : Register) : (inputHead nodePC pointer).length = 15 := rfl

theorem inputCode_length (start : Nat) (pointer : Register) : (inputCode start pointer).length = 87 := rfl

def readROM (start : Nat) (region : Region) (pointer : Register) : List PackingOp :=
  match region with
  | .input => inputCode start pointer
  | .internal => InternalInput.code pointer
  | .children => relativeRead (registerOffset pointer) .index ++ [.base (.base (.loadROM .children .value .index))]

/-- Every port is concrete static code. No mathematical result, safety/cost
contract, dimension or runtime heap is an argument to the selected code. -/
def ports : BuilderPorts :=
  { readROM := readROM, readHeap := ConcreteHeap.read, writeHeap := ConcreteHeap.write }

def program : List PackingOp := fullBuildCode ports

theorem program_fixed : program = lowerProgram ports fullBuild 0 0 := rfl

theorem source_no_children (N q t : Nat) (op : Op)
    (hm : op ∈ PA17TableBuild005.buildProgram N q t) : plainReadsChildren op = false :=
  original_buildProgram_no_children N q t op hm

theorem inputHead_prefix_frame (rom : PhysicalROM) (nodePC : Nat) (pointer : Register)
    (state : WordState bits) (count : Nat) :
    (executeOps rom ((inputHead nodePC pointer).take count) state).heap = state.heap ∧
      (executeOps rom ((inputHead nodePC pointer).take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 15
  · interval_cases count <;>
      simp [inputHead, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [inputHead_length]; omega)]
    exact ⟨rfl, rfl⟩

theorem inputHead_pc (rom : PhysicalROM) (nodePC : Nat) (pointer : Register)
    (N q : Nat) (state : WordState bits)
    (hN : (state.heap (state.register .address)).toNat = N)
    (hq : (state.heap (state.register .address + BitVec.ofNat bits 1)).toNat = q)
    (hs : Fits bits (N * q + 3)) :
    (executeOps rom (inputHead nodePC pointer) state).pc =
      if N * q + 3 ≤ (Ordinary.pointerValue state pointer).toNat then BitVec.ofNat bits nodePC
      else state.pc + BitVec.ofNat bits 75 := by
  have h3 : 3 < 2 ^ bits := lt_of_le_of_lt (by omega) hs
  have hmul : N * q < 2 ^ bits := lt_of_le_of_lt (by omega) hs
  have hdiff : N * q + 3 - (Ordinary.pointerValue state pointer).toNat < 2 ^ bits :=
    lt_of_le_of_lt (Nat.sub_le _ _) hs
  unfold Ordinary.pointerValue at hdiff ⊢
  simp [inputHead, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction, packingArithmetic,
    hN, hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hdiff, Nat.sub_eq_zero_iff_le,
    BitVec.ofNat_add_ofNat, BitVec.add_assoc]

theorem inputHead_run (rom : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false)
    (hcode : WordsFit bits (packingCode (left ++ inputCode left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ inputCode left.length pointer ++ right).length)) :
    packingRun rom (left ++ inputCode left.length pointer ++ right) 15 state =
      executeOps rom (inputHead (5 * (left.length + 24)) pointer) state := by
  let headCode := inputHead (5 * (left.length + 24)) pointer
  let lead := headCode.take 14
  have hlen : lead.length = 14 := rfl
  apply PSTRWordSegments.segment_last rom _ lead (.jumpIfZero .flag .index) left.length
    (by simp only [List.length_append, inputCode_length, hlen]; omega) ?_ ?_ ?_ hcode hpcfit state hpc ha
  · intro position hp
    have hh := PA17UniformGenerator035a.segment_index left headCode
      (StageInput.code pointer ++ forwardJump (5 * (left.length + 87)) ++
        NodeInput.nodeBitCode (left.length + 24) pointer ++ right) position
      (by rw [hlen] at hp; change position < 15; omega)
    simpa only [inputCode, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := PA17UniformGenerator035a.segment_index left headCode
      (StageInput.code pointer ++ forwardJump (5 * (left.length + 87)) ++
        NodeInput.nodeBitCode (left.length + 24) pointer ++ right) 14 (by change 14 < 15; decide)
    have he : headCode[14]'(by change 14 < 15; decide) = PackingOp.jumpIfZero .flag .index := rfl
    rw [he] at hh
    simpa only [inputCode, List.append_assoc, hlen] using hh
  · simp [lead, headCode, inputHead, relativeRead, StraightProgram, StraightOp]

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.ConcreteAST
