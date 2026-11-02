module

public import Structure.PSTR_BuildLower_Dispatch_018

/-! Actual fetched Word control of the fixed double-cutoff dispatcher.
Packed/ordinary outputs are their actual instruction executions, not answers
supplied by a contract. Concrete packed semantic/frame lemmas plug in later. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchRun

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  PA17UniformGenerator035a

variable {bits : Nat}

def code (packed ordinary : List PackingOp) (start : Nat) (pointer : Register) : List PackingOp :=
  memoryClassify pointer (5 * (start + 9 + packed.length + 3)) ++ packed ++
    forwardJump (5 * (start + 9 + packed.length + 3 + ordinary.length)) ++ ordinary

theorem code_length (packed ordinary : List PackingOp) (start : Nat) (pointer : Register) :
    (code packed ordinary start pointer).length = packed.length + ordinary.length + 12 := by
  simp only [code, List.length_append, memoryClassify_length, forwardJump_length]
  omega

theorem code_read (packed : List PackingOp) (start : Nat) (pointer : Register) :
    code packed (Ordinary.read pointer) start pointer = readDispatcher packed start pointer := by
  simp only [code, Ordinary.read_length, readDispatcher]

theorem code_write (packed : List PackingOp) (start : Nat) (pointer : Register) :
    code packed (Ordinary.write pointer) start pointer = writeDispatcher packed start pointer := by
  simp only [code, Ordinary.write_length, writeDispatcher]

theorem classify_run (rom : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (hcode : WordsFit bits (packingCode (left ++ code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code packed ordinary left.length pointer ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length))
    (ha : state.halted = false) :
    packingRun rom (left ++ code packed ordinary left.length pointer ++ right) 9 state =
      executeOps rom (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state := by
  let classify := memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))
  let lead := classify.take 8
  have hlen : lead.length = 8 := rfl
  have hblock := code_length packed ordinary left.length pointer
  apply PSTRWordSegments.segment_last rom _ lead (.jumpIfZero .flag .fresh) left.length
    (by simp only [List.length_append, hlen, hblock]; omega) ?_ ?_ ?_ hcode hpcfit state hpc ha
  · intro i hi
    have hh := segment_index left classify
      (packed ++ forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right)
      i (by rw [hlen] at hi; change i < 9; omega)
    simpa only [code, List.append_assoc, lead, List.getElem_take] using hh
  · have hh := segment_index left classify
      (packed ++ forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right)
      8 (by change 8 < 9; decide)
    have hj : classify[8]'(by change 8 < 9; decide) = PackingOp.jumpIfZero .flag .fresh := rfl
    rw [hj] at hh
    simpa only [code, List.append_assoc, hlen] using hh
  · simp [lead, classify, memoryClassify, relativeRead, StraightProgram, StraightOp]

theorem packed_run (rom : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (hs : StraightProgram packed)
    (hcode : WordsFit bits (packingCode (left ++ code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code packed ordinary left.length pointer ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 9)))
    (ha : state.halted = false) :
    packingRun rom (left ++ code packed ordinary left.length pointer ++ right) packed.length state =
      executeOps rom packed state := by
  have hblock := code_length packed ordinary left.length pointer
  apply PSTRWordSegments.straight_segment rom _ packed (left.length + 9)
    (by simp only [List.length_append, hblock]; omega) ?_ hs hcode hpcfit state hpc ha
  intro i hi
  have hh := segment_index
    (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) packed
    (forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)) ++ ordinary ++ right) i hi
  simpa only [code, List.append_assoc, List.length_append, memoryClassify_length] using hh

theorem ordinary_run (rom : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (hs : StraightProgram ordinary)
    (hcode : WordsFit bits (packingCode (left ++ code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code packed ordinary left.length pointer ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 9 + packed.length + 3)))
    (ha : state.halted = false) :
    packingRun rom (left ++ code packed ordinary left.length pointer ++ right) ordinary.length state =
      executeOps rom ordinary state := by
  have hblock := code_length packed ordinary left.length pointer
  apply PSTRWordSegments.straight_segment rom _ ordinary (left.length + 9 + packed.length + 3)
    (by simp only [List.length_append, hblock]; omega) ?_ hs hcode hpcfit state hpc ha
  intro i hi
  have hh := segment_index
    (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3)) ++ packed ++
      forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length))) ordinary right i hi
  simpa only [code, List.append_assoc, List.length_append, memoryClassify_length, forwardJump_length,
    Nat.add_assoc] using hh

theorem jump_run (rom : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (hcode : WordsFit bits (packingCode (left ++ code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code packed ordinary left.length pointer ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * (left.length + 9 + packed.length)))
    (ha : state.halted = false) :
    packingRun rom (left ++ code packed ordinary left.length pointer ++ right) 3 state =
      executeOps rom (forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length))) state := by
  let jump := forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length))
  let lead := jump.take 2
  have hlen : lead.length = 2 := rfl
  have hblock := code_length packed ordinary left.length pointer
  apply PSTRWordSegments.segment_last rom _ lead (.jumpIfZero .flag .fresh) (left.length + 9 + packed.length)
    (by simp only [List.length_append, hlen, hblock]; omega) ?_ ?_ ?_ hcode hpcfit state hpc ha
  · intro i hi
    have hh := segment_index
      (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3)) ++ packed)
      jump (ordinary ++ right) i (by rw [hlen] at hi; change i < 3; omega)
    simpa only [code, List.append_assoc, List.length_append, memoryClassify_length, lead, List.getElem_take,
      jump, Nat.add_assoc] using hh
  · have hh := segment_index
      (left ++ memoryClassify pointer (5 * (left.length + 9 + packed.length + 3)) ++ packed)
      jump (ordinary ++ right) 2 (by change 2 < 3; decide)
    have hj : jump[2]'(by change 2 < 3; decide) = PackingOp.jumpIfZero .flag .fresh := rfl
    rw [hj] at hh
    simpa only [code, List.append_assoc, List.length_append, memoryClassify_length, hlen, jump, Nat.add_assoc] using hh
  · simp [lead, jump, forwardJump, StraightProgram, StraightOp]

def ordinaryCase (pointer : Register) (state : WordState bits) : Prop :=
  (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤ (Ordinary.pointerValue state pointer).toNat

instance ordinaryCaseDecidable (pointer : Register) (state : WordState bits) :
    Decidable (ordinaryCase pointer state) :=
  inferInstanceAs (Decidable ((state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤
    (Ordinary.pointerValue state pointer).toNat))

def steps (packed ordinary : List PackingOp) (pointer : Register) (state : WordState bits) : Nat :=
  if ordinaryCase pointer state then 9 + ordinary.length else 9 + packed.length + 3

def result (rom : PhysicalROM) (left packed ordinary : List PackingOp) (pointer : Register)
    (state : WordState bits) : WordState bits :=
  let tested := executeOps rom (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state
  if ordinaryCase pointer state then executeOps rom ordinary tested else
    executeOps rom (forwardJump (5 * (left.length + 9 + packed.length + 3 + ordinary.length)))
      (executeOps rom packed tested)

theorem run (rom : PhysicalROM) (left packed ordinary right : List PackingOp) (pointer : Register)
    (hp : StraightProgram packed) (ho : StraightProgram ordinary)
    (hcode : WordsFit bits (packingCode (left ++ code packed ordinary left.length pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ code packed ordinary left.length pointer ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length)) (ha : state.halted = false) :
    packingRun rom (left ++ code packed ordinary left.length pointer ++ right) (steps packed ordinary pointer state) state =
      result rom left packed ordinary pointer state := by
  let tested := executeOps rom (memoryClassify pointer (5 * (left.length + 9 + packed.length + 3))) state
  have htactive : tested.halted = false := (executeOps_halted rom _ state).trans ha
  by_cases hg : ordinaryCase pointer state
  · have hgraw : (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have htpc : tested.pc = BitVec.ofNat bits (5 * (left.length + 9 + packed.length + 3)) := by
      rw [memoryClassify_pc, ite_eq_left hgraw]
    simp only [steps, result, hg, ite_true]
    rw [PSTRWordSegments.run_add, classify_run rom left packed ordinary right pointer hcode hpcfit state hpc ha,
      ordinary_run rom left packed ordinary right pointer ho hcode hpcfit tested htpc htactive]
  · have hgraw : ¬ (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat ≤
        (Ordinary.pointerValue state pointer).toNat := hg
    have htpc : tested.pc = BitVec.ofNat bits (5 * (left.length + 9)) := by
      have he : 5 * left.length + 45 = 5 * (left.length + 9) := by omega
      rw [memoryClassify_pc, ite_eq_right hgraw, hpc, BitVec.ofNat_add_ofNat, he]
    have hppc : (executeOps rom packed tested).pc =
        BitVec.ofNat bits (5 * (left.length + 9 + packed.length)) := by
      have he : 5 * (left.length + 9) + 5 * packed.length = 5 * (left.length + 9 + packed.length) := by omega
      rw [executeOps_pc rom packed tested hp, htpc, BitVec.ofNat_add_ofNat, he]
    have hpactive : (executeOps rom packed tested).halted = false :=
      (executeOps_halted rom packed tested).trans htactive
    simp only [steps, result, hg, ite_false]
    rw [PSTRWordSegments.run_add, PSTRWordSegments.run_add,
      classify_run rom left packed ordinary right pointer hcode hpcfit state hpc ha,
      packed_run rom left packed ordinary right pointer hp hcode hpcfit tested htpc htactive,
      jump_run rom left packed ordinary right pointer hcode hpcfit _ hppc hpactive]

theorem steps_le_code (packed ordinary : List PackingOp) (start : Nat) (pointer : Register)
    (state : WordState bits) : steps packed ordinary pointer state ≤ (code packed ordinary start pointer).length := by
  unfold steps
  split <;> rw [code_length] <;> omega

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.DispatchRun
