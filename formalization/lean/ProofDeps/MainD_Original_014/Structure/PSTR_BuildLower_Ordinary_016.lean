module

public import Structure.PSTR_BuildLower_RelativeValue_011

/-! Fixed ordinary-word old-A17 heap ports. The shared actual bank contains
C0 at offset3 and oldIndexBase at offset6. The source VM pointer is read from
its actual bank slot; source addresses are rebased only after subtracting C0.
No new physical allocation or dimension-dependent immediate is introduced. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.Ordinary

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

variable {bits : Nat}

def pointerValue (state : WordState bits) (pointer : Register) : BitVec bits :=
  state.heap (state.register .address + BitVec.ofNat bits (registerOffset pointer))

def targetAddress (state : WordState bits) (pointer : Register) : BitVec bits :=
  state.heap (state.register .address + BitVec.ofNat bits 6) +
    BitVec.ofNat bits ((pointerValue state pointer).toNat -
      (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat)

def addressCode (pointer : Register) : List PackingOp :=
  relativeRead (registerOffset pointer) .old ++ relativeRead 3 .fresh ++
    [.base (.subtract .old .old .fresh)] ++ relativeRead 6 .fresh ++
    [.base (.base (.add .index .fresh .old))]

def read (pointer : Register) : List PackingOp :=
  addressCode pointer ++ [.base (.base (.loadHeap .value .index))]

def write (pointer : Register) : List PackingOp :=
  addressCode pointer ++ [.base (.base (.storeHeap .index .value))]

theorem read_length (pointer : Register) : (read pointer).length = 12 := rfl
theorem write_length (pointer : Register) : (write pointer).length = 12 := rfl

theorem read_straight (pointer : Register) : StraightProgram (read pointer) := by
  simp [read, addressCode, relativeRead, StraightProgram, StraightOp]

theorem write_straight (pointer : Register) : StraightProgram (write pointer) := by
  simp [write, addressCode, relativeRead, StraightProgram, StraightOp]

theorem read_value (rom : PhysicalROM) (pointer : Register) (state : WordState bits) :
    (executeOps rom (read pointer) state).register .value = state.heap (targetAddress state pointer) := by
  simp [read, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    targetAddress, pointerValue]

theorem read_prefix_heap (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (count : Nat) : (executeOps rom ((read pointer).take count) state).heap = state.heap := by
  by_cases hc : count ≤ 12
  · interval_cases count <;>
      simp [read, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [read_length]; omega)]
    rfl

theorem read_prefix_base (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (count : Nat) :
    (executeOps rom ((read pointer).take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 12
  · interval_cases count <;>
      simp [read, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [read_length]; omega)]
    rfl

theorem write_heap (rom : PhysicalROM) (pointer : Register) (state : WordState bits) :
    (executeOps rom (write pointer) state).heap =
      Function.update state.heap (targetAddress state pointer) (state.register .value) := by
  simp [write, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
    targetAddress, pointerValue]

theorem write_prefix_base (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (count : Nat) :
    (executeOps rom ((write pointer).take count) state).register .address = state.register .address := by
  by_cases hc : count ≤ 12
  · interval_cases count <;>
      simp [write, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [write_length]; omega)]
    rfl

theorem write_prefix_frame (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (point : BitVec bits) (hne : point ≠ targetAddress state pointer) (count : Nat) :
    (executeOps rom ((write pointer).take count) state).heap point = state.heap point := by
  by_cases hc : count < 12
  · interval_cases count <;>
      simp [write, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction]
  · rw [List.take_of_length_le (by rw [write_length]; omega), write_heap, Function.update_of_ne hne]

theorem read_access (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (heapWords count : Nat)
    (hptr : (state.register .address + BitVec.ofNat bits (registerOffset pointer)).toNat < heapWords)
    (hc0 : (state.register .address + BitVec.ofNat bits 3).toNat < heapWords)
    (hindex : (state.register .address + BitVec.ofNat bits 6).toNat < heapWords)
    (htarget : (targetAddress state pointer).toNat < heapWords) (hc : count < 12) :
    packingAccessFits rom heapWords (executeOps rom ((read pointer).take count) state)
      ((read pointer)[count]'(by simpa only [read_length] using hc)) := by
  unfold targetAddress pointerValue at htarget
  have hs : (state.heap (state.register .address + BitVec.ofNat bits (registerOffset pointer))).toNat -
      (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (state.heap _).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs] at htarget
  simp [BitVec.toNat_add] at hptr hc0 hindex
  interval_cases count <;>
    simp [read, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits] <;> assumption

theorem write_access (rom : PhysicalROM) (pointer : Register) (state : WordState bits)
    (heapWords count : Nat)
    (hptr : (state.register .address + BitVec.ofNat bits (registerOffset pointer)).toNat < heapWords)
    (hc0 : (state.register .address + BitVec.ofNat bits 3).toNat < heapWords)
    (hindex : (state.register .address + BitVec.ofNat bits 6).toNat < heapWords)
    (htarget : (targetAddress state pointer).toNat < heapWords) (hc : count < 12) :
    packingAccessFits rom heapWords (executeOps rom ((write pointer).take count) state)
      ((write pointer)[count]'(by simpa only [write_length] using hc)) := by
  unfold targetAddress pointerValue at htarget
  have hs : (state.heap (state.register .address + BitVec.ofNat bits (registerOffset pointer))).toNat -
      (state.heap (state.register .address + BitVec.ofNat bits 3)).toNat < 2 ^ bits :=
    (Nat.sub_le _ _).trans_lt (state.heap _).isLt
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs] at htarget
  simp [BitVec.toNat_add] at hptr hc0 hindex
  interval_cases count <;>
    simp [write, addressCode, relativeRead, executeOps, packingExecuteOp, wordOp, wordInstruction,
      packingAccessFits, AccessFits] <;> assumption

theorem targetAddress_eq (pointer : Register) (state : WordState bits) (a C0 indexBase : Nat)
    (ha : Fits bits a) (hC0 : Fits bits C0)
    (hptr : pointerValue state pointer = BitVec.ofNat bits a)
    (hc : state.heap (state.register .address + BitVec.ofNat bits 3) = BitVec.ofNat bits C0)
    (hi : state.heap (state.register .address + BitVec.ofNat bits 6) = BitVec.ofNat bits indexBase) :
    targetAddress state pointer = BitVec.ofNat bits (indexBase + (a - C0)) := by
  unfold targetAddress
  rw [hptr, hc, hi]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hC0,
    BitVec.ofNat_add_ofNat]

theorem targetAddress_room (pointer : Register) (state : WordState bits) (a C0 indexBase I heapWords : Nat)
    (ha : Fits bits a) (hC0 : Fits bits C0) (hheap : Fits bits heapWords)
    (hptr : pointerValue state pointer = BitVec.ofNat bits a)
    (hc : state.heap (state.register .address + BitVec.ofNat bits 3) = BitVec.ofNat bits C0)
    (hi : state.heap (state.register .address + BitVec.ofNat bits 6) = BitVec.ofNat bits indexBase)
    (hoffset : a - C0 < I) (hroom : indexBase + I ≤ heapWords) :
    (targetAddress state pointer).toNat = indexBase + (a - C0) ∧
      (targetAddress state pointer).toNat < heapWords := by
  have htarget : indexBase + (a - C0) < heapWords := by omega
  rw [targetAddress_eq pointer state a C0 indexBase ha hC0 hptr hc hi, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (htarget.trans hheap)]
  exact ⟨rfl, htarget⟩

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.Ordinary
