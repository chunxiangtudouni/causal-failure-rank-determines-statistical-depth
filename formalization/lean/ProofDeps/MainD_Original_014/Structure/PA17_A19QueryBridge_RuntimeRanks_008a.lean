module

public import Structure.PA17_QueryRanks_011
public import Structure.PSTR_HD_WordSegments_014
public import PaperProofs.Structure.PackedCapacityRAM

/-! One fixed 51-op rank kernel, independent of every input dimension and
word width. The only assembly parameter is its containing-code origin.
address is the actual physical query header and remains unchanged. q is
loaded from original input[1]; both budget scans use one real reverse loop.
No scratch heap, helper HALT, state reset or generated code is used. -/

@[expose] public section
set_option maxRecDepth 16000
set_option maxHeartbeats 1600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM

def setup : List PackingOp :=
  [.base (.base (.constant .index 1)), .base (.base (.loadROM .input .total .index)),
   .base (.base (.constant .flag 2)), .base (.base (.add .total .total .flag)),
   .base (.base (.constant .old 0)), .base (.base (.add .index .total .old)),
   .base (.base (.add .value .total .old)), .base (.base (.add .fresh .total .old))]

def testLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .old (5 * (origin + 23))))]

def testBlock (origin : Nat) : List PackingOp := testLead origin ++ [.jumpIfZero .index .old]

def bodyLead (origin : Nat) : List PackingOp :=
  [.base (.base (.constant .flag 1)), .base (.subtract .index .index .flag),
   .base (.base (.constant .old 16)), .base (.base (.add .old .address .old)),
   .base (.base (.add .old .old .index)), .base (.base (.loadHeap .flag .old)),
   .base (.base (.select .value .flag .value .index)), .base (.base (.add .old .old .total)),
   .base (.base (.loadHeap .flag .old)), .base (.base (.select .fresh .flag .fresh .index)),
   .base (.base (.constant .flag 0)), .base (.base (.constant .old (5 * (origin + 8))))]

def bodyBlock (origin : Nat) : List PackingOp := bodyLead origin ++ [.jumpIfZero .flag .old]

def footer : List PackingOp :=
  [.base (.base (.constant .old 4)), .base (.base (.add .old .address .old)),
   .base (.base (.storeHeap .old .value)), .base (.base (.constant .flag 1)),
   .base (.base (.add .old .old .flag)), .base (.base (.storeHeap .old .fresh)),
   .base (.subtract .index .fresh .flag), .base (.base (.add .old .old .flag)),
   .base (.base (.storeHeap .old .index)), .base (.base (.constant .index 2)),
   .base (.base (.add .index .address .index)), .base (.base (.loadHeap .index .index)),
   .base (.base (.constant .flag 0)), .base (.base (.constant .value 1)),
   .base (.base (.select .flag .fresh .value .flag)), .base (.base (.select .flag .index .flag .index)),
   .base (.base (.add .old .old .value)), .base (.base (.storeHeap .old .flag)),
   .base (.base (.constant .old 4)), .base (.base (.add .old .address .old)),
   .base (.base (.loadHeap .old .old)), .base (.base (.add .value .fresh .value)),
   .base (.base (.minimum .value .old .value)), .base (.base (.select .old .index .old .total)),
   .base (.base (.select .value .index .value .total)), .base (.base (.constant .flag 0)),
   .base (.base (.select .fresh .index .fresh .flag)), .base (.base (.constant .index 0))]

def programAt (origin : Nat) : List PackingOp := setup ++ testBlock origin ++ bodyBlock origin ++ footer

def steps (q : Nat) : Nat := 15 * (q + 2) + 38

theorem setup_length : setup.length = 8 := rfl
theorem testLead_length (origin : Nat) : (testLead origin).length = 1 := rfl
theorem testBlock_length (origin : Nat) : (testBlock origin).length = 2 := rfl
theorem bodyLead_length (origin : Nat) : (bodyLead origin).length = 12 := rfl
theorem bodyBlock_length (origin : Nat) : (bodyBlock origin).length = 13 := rfl
theorem footer_length : footer.length = 28 := rfl
theorem programAt_length (origin : Nat) : (programAt origin).length = 51 := rfl

theorem setup_straight : StraightProgram setup := by simp [setup, StraightProgram, StraightOp]
theorem testLead_straight (origin : Nat) : StraightProgram (testLead origin) := by
  simp [testLead, StraightProgram, StraightOp]
theorem bodyLead_straight (origin : Nat) : StraightProgram (bodyLead origin) := by
  simp [bodyLead, StraightProgram, StraightOp]
theorem footer_straight : StraightProgram footer := by simp [footer, StraightProgram, StraightOp]

theorem setup_noStore : ∀ op ∈ setup, HeapPreservingOp op := by simp [setup, HeapPreservingOp]
theorem test_noStore (origin : Nat) : ∀ op ∈ testBlock origin, HeapPreservingOp op := by
  simp [testBlock, testLead, HeapPreservingOp]
theorem body_noStore (origin : Nat) : ∀ op ∈ bodyBlock origin, HeapPreservingOp op := by
  simp [bodyBlock, bodyLead, HeapPreservingOp]

def suffix (q remaining : Nat) (test : Nat → Bool) : Nat :=
  ((List.range' remaining (q + 2 - remaining)).find? (fun budget => !(test budget))).getD (q + 2)

theorem suffix_init (q : Nat) (test : Nat → Bool) : suffix q (q + 2) test = q + 2 := by
  simp [suffix]

theorem suffix_final (q : Nat) (test : Nat → Bool) :
    suffix q 0 test = PA17QueryRanks011.firstFalseValue q test := by
  rfl

theorem suffix_step (q remaining : Nat) (test : Nat → Bool) (hr : remaining < q + 2) :
    suffix q remaining test = if test remaining then suffix q (remaining + 1) test else remaining := by
  have he : q + 2 - remaining = (q + 2 - (remaining + 1)) + 1 := by omega
  unfold suffix
  rw [he, List.range'_succ]
  cases ht : test remaining <;> simp [ht]

theorem suffix_bound (q remaining : Nat) (test : Nat → Bool) : suffix q remaining test ≤ q + 2 := by
  unfold suffix
  cases hh : (List.range' remaining (q + 2 - remaining)).find? (fun budget => !(test budget)) with
  | none => simp
  | some value =>
    have hm := List.mem_of_find?_eq_some hh
    obtain ⟨index, hi, heq⟩ := List.mem_range'.mp hm
    simp only [Option.getD_some]
    omega

theorem execute_setup {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits)
    (h1 : Fits bits 1) (hq : (rom.words .input).getD 1 0 = q) :
    let after := executeOps rom setup state
    after.register .address = state.register .address ∧
      after.register .total = BitVec.ofNat bits (q + 2) ∧
      after.register .index = BitVec.ofNat bits (q + 2) ∧
      after.register .value = BitVec.ofNat bits (q + 2) ∧
      after.register .fresh = BitVec.ofNat bits (q + 2) ∧ after.heap = state.heap := by
  change (rom.words .input)[1]?.getD 0 = q at hq
  simp +decide [setup, executeOps, packingExecuteOp, wordOp, wordInstruction,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1, hq,
    BitVec.ofNat_add_ofNat]

theorem execute_test {bits : Nat} (rom : PhysicalROM) (origin remaining : Nat) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 8)))
    (hi : state.register .index = BitVec.ofNat bits remaining) (hf : Fits bits remaining) :
    (executeOps rom (testBlock origin) state).pc =
      BitVec.ofNat bits (5 * (origin + if remaining = 0 then 23 else 10)) ∧
      (executeOps rom (testBlock origin) state).heap = state.heap := by
  have he : 5 * (origin + 8) + 5 + 5 = 5 * (origin + 10) := by omega
  by_cases hz : remaining = 0 <;>
   simp +decide [testBlock, testLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, hi, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hf,
    BitVec.ofNat_add_ofNat, he, hz]

theorem execute_body {bits : Nat} (rom : PhysicalROM) (origin q header remaining good bad : Nat)
    (state : WordState bits) (h1 : Fits bits 1) (hr : Fits bits (remaining + 1))
    (hp : state.register .address = BitVec.ofNat bits header)
    (hi : state.register .index = BitVec.ofNat bits (remaining + 1))
    (ht : state.register .total = BitVec.ofNat bits (q + 2))
    (hg : state.register .value = BitVec.ofNat bits good)
    (hb : state.register .fresh = BitVec.ofNat bits bad) :
    let after := executeOps rom (bodyBlock origin) state
    after.register .address = BitVec.ofNat bits header ∧
      after.register .total = BitVec.ofNat bits (q + 2) ∧
      after.register .index = BitVec.ofNat bits remaining ∧
      after.register .value =
        (if (state.heap (BitVec.ofNat bits (header + 16 + remaining))).toNat = 0
          then BitVec.ofNat bits remaining else BitVec.ofNat bits good) ∧
      after.register .fresh =
        (if (state.heap (BitVec.ofNat bits (header + 16 + remaining + (q + 2)))).toNat = 0
          then BitVec.ofNat bits remaining else BitVec.ofNat bits bad) ∧
      after.heap = state.heap ∧ after.pc = BitVec.ofNat bits (5 * (origin + 8)) := by
  simp +decide [bodyBlock, bodyLead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    hp, hi, ht, hg, hb, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt hr,
    BitVec.ofNat_add_ofNat, Nat.add_assoc]

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeRanks008
