module

public import Structure.PSTR_BuildLower_Ordinary_016

/-! Real fixed decoding of the node-incidence portion of the OLD given-tree
input address. Dimensions and source pointer are physically read from bank;
old/fresh become quotient/remainder for the real A06 node-bit caller. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

variable {bits : Nat}

def prep (pointer : Register) : List PackingOp :=
  relativeRead (registerOffset pointer) .old ++ relativeRead 0 .total ++ relativeRead 1 .value ++
    [.arithmetic .multiply .total .total .value,
     .base (.base (.constant .fresh 3)),
     .base (.base (.add .total .total .fresh)),
     .base (.subtract .old .old .total),
     .arithmetic .divide .index .old .value,
     .arithmetic .multiply .fresh .index .value,
     .base (.subtract .fresh .old .fresh),
     .base (.base (.minimum .old .index .index))]

theorem prep_length (pointer : Register) : (prep pointer).length = 17 := rfl

theorem prep_straight (pointer : Register) : StraightProgram (prep pointer) := by
  simp [prep, relativeRead, StraightProgram, StraightOp]

theorem prep_prefix_frame (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (count : Nat) :
    (executeOps rom ((prep pointer).take count) state).heap = state.heap ∧
      (executeOps rom ((prep pointer).take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 17
  · interval_cases count <;>
      simp [prep, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [prep_length]; omega)]
    exact ⟨rfl, rfl⟩

theorem prep_pc (rom : PhysicalROM) (pointer : Register) (state : WordState bits) :
    (executeOps rom (prep pointer) state).pc = state.pc + BitVec.ofNat bits 85 :=
  executeOps_pc rom _ state (prep_straight pointer)

theorem prep_value (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (N q payload : Nat)
    (hN : (state.heap (state.register .address)).toNat = N)
    (hq : (state.heap (state.register .address + BitVec.ofNat bits 1)).toNat = q)
    (hp : (Ordinary.pointerValue state pointer).toNat = 3 + N * q + payload) :
    let after := executeOps rom (prep pointer) state
    (after.register .old).toNat = payload / q ∧ (after.register .fresh).toNat = payload % q := by
  have hinput : 3 + N * q + payload < 2 ^ bits := by
    rw [← hp]
    exact (Ordinary.pointerValue state pointer).isLt
  have hNq3 : N * q + 3 < 2 ^ bits := by omega
  have hpay : payload < 2 ^ bits := by omega
  have hdiv : payload / q < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hpay
  have hmul : payload / q * q < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hpay
  have hrem : payload % q < 2 ^ bits := (Nat.mod_le _ _).trans_lt hpay
  have hsub : 3 + N * q + payload - (N * q + 3) = payload := by omega
  have hmod : payload - payload / q * q = payload % q := Nat.mod_eq_sub_div_mul.symm
  unfold Ordinary.pointerValue at hp
  simp [prep, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction, packingArithmetic,
    hN, hq, hp, BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat,
    Nat.mod_eq_of_lt hNq3, Nat.mod_eq_of_lt hpay,
    Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hmul, Nat.mod_eq_of_lt hrem, hsub, hmod]

theorem prep_node_tool (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (N q node : Nat) (tool : Fin q)
    (hN : (state.heap (state.register .address)).toNat = N)
    (hq : (state.heap (state.register .address + BitVec.ofNat bits 1)).toNat = q)
    (hp : (Ordinary.pointerValue state pointer).toNat = 3 + N * q + (node * q + tool.val)) :
    let after := executeOps rom (prep pointer) state
    (after.register .old).toNat = node ∧ (after.register .fresh).toNat = tool.val := by
  have hh := prep_value rom pointer state N q (node * q + tool.val) hN hq hp
  have hqpos : 0 < q := lt_of_le_of_lt (Nat.zero_le tool.val) tool.isLt
  have hquot : (node * q + tool.val) / q = node := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hqpos,
      Nat.div_eq_of_lt tool.isLt, Nat.zero_add]
  have hmod : (node * q + tool.val) % q = tool.val := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt tool.isLt]
  simpa only [hquot, hmod] using hh

theorem prep_run (rom : PhysicalROM) (left right : List PackingOp) (pointer : Register)
    (hcode : WordsFit bits (packingCode (left ++ prep pointer ++ right)))
    (hpcfit : Fits bits (5 * (left ++ prep pointer ++ right).length))
    (state : WordState bits) (hpc : state.pc = BitVec.ofNat bits (5 * left.length))
    (ha : state.halted = false) :
    packingRun rom (left ++ prep pointer ++ right) 17 state = executeOps rom (prep pointer) state := by
  apply PSTRWordSegments.straight_segment rom _ (prep pointer) left.length
    (by simp only [List.length_append]; omega)
    (PA17UniformGenerator035a.segment_index left (prep pointer) right) (prep_straight pointer)
    hcode hpcfit state hpc ha

theorem prep_prefix_access (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (heapWords count : Nat)
    (hptr : (state.register .address + BitVec.ofNat bits (registerOffset pointer)).toNat < heapWords)
    (hN : (state.register .address).toNat < heapWords)
    (hq : (state.register .address + BitVec.ofNat bits 1).toNat < heapWords) (hc : count < 17) :
    packingAccessFits rom heapWords (executeOps rom ((prep pointer).take count) state)
      ((prep pointer)[count]'(by simpa only [prep_length] using hc)) := by
  simp [BitVec.toNat_add] at hptr hq
  interval_cases count <;>
    simp [prep, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits] <;> assumption

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput
