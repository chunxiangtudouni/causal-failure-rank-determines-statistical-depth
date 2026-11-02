module

public import Structure.PSTR_BuildLower_ExprFrame_002

/-! Inline literal ALU lowering. The bank is a map of real physical addresses;
this module fixes neither A06's header nor its cache/control allocation. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine

variable {bits : Nat}

def bankRegisters (bank : Register → Nat) (heap : BitVec bits → BitVec bits)
    (reg : Register) : BitVec bits := heap (BitVec.ofNat bits (bank reg))

def readBank (bank : Register → Nat) (target source : Register) : List PackingOp :=
  [.base (.base (.constant .address (bank source))),
   .base (.base (.loadHeap target .address))]

theorem readBank_value (rom : PhysicalROM) (bank : Register → Nat)
    (target source : Register) (state : WordState bits) :
    (executeOps rom (readBank bank target source) state).register target =
      bankRegisters bank state.heap source := by
  simp [readBank, executeOps, packingExecuteOp, wordOp, wordInstruction,
    bankRegisters]

theorem readBank_prefix_frame (rom : PhysicalROM) (bank : Register → Nat)
    (target source : Register) (point : BitVec bits) :
    WordPrefixFrame rom (readBank bank target source) point := by
  intro state count
  cases count with
  | zero => rfl
  | succ count => cases count <;>
      simp [readBank, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem bankRegisters_update (bank : Register → Nat)
    (hi : Function.Injective (fun reg => BitVec.ofNat bits (bank reg)))
    (heap : BitVec bits → BitVec bits) (target : Register) (value : BitVec bits) :
    bankRegisters bank (Function.update heap (BitVec.ofNat bits (bank target)) value) =
      Function.update (bankRegisters bank heap) target value := by
  funext reg
  by_cases he : reg = target
  · subst reg
    simp only [bankRegisters, Function.update_self]
  · have hn : BitVec.ofNat bits (bank reg) ≠ BitVec.ofNat bits (bank target) :=
      fun hh => he (hi hh)
    simp only [bankRegisters, Function.update_of_ne hn, Function.update_of_ne he]

inductive ValueOp where
  | constant (target : Register) (value : Nat)
  | add (target left right : Register)
  | minimum (target left right : Register)
  | select (target condition whenTrue whenFalse : Register)
  | subtract (target left right : Register)

def ValueOp.target : ValueOp → Register
  | .constant target _ | .add target _ _ | .minimum target _ _ |
    .select target _ _ _ | .subtract target _ _ => target

def ValueOp.original : ValueOp → Op
  | .constant target value => .base (.constant target value)
  | .add target left right => .base (.add target left right)
  | .minimum target left right => .base (.minimum target left right)
  | .select target condition whenTrue whenFalse =>
      .base (.select target condition whenTrue whenFalse)
  | .subtract target left right => .subtract target left right

def ValueOp.value (registers : Register → BitVec bits) : ValueOp → BitVec bits
  | .constant _ value => BitVec.ofNat bits value
  | .add _ left right => registers left + registers right
  | .minimum _ left right =>
      if (registers left).toNat ≤ (registers right).toNat then registers left else registers right
  | .select _ condition whenTrue whenFalse =>
      if (registers condition).toNat = 0 then registers whenFalse else registers whenTrue
  | .subtract _ left right =>
      BitVec.ofNat bits ((registers left).toNat - (registers right).toNat)

def ValueOp.lower (bank : Register → Nat) : ValueOp → List PackingOp
  | .constant target value =>
      [.base (.base (.constant .value value))] ++ writeControl (bank target)
  | .add target left right =>
      readBank bank .old left ++ readBank bank .fresh right ++
        [.base (.base (.add .value .old .fresh))] ++ writeControl (bank target)
  | .minimum target left right =>
      readBank bank .old left ++ readBank bank .fresh right ++
        [.base (.base (.minimum .value .old .fresh))] ++ writeControl (bank target)
  | .select target condition whenTrue whenFalse =>
      readBank bank .flag condition ++ readBank bank .old whenTrue ++
        readBank bank .fresh whenFalse ++
        [.base (.base (.select .value .flag .old .fresh))] ++ writeControl (bank target)
  | .subtract target left right =>
      readBank bank .old left ++ readBank bank .fresh right ++
        [.base (.subtract .value .old .fresh)] ++ writeControl (bank target)

theorem valueOp_lower_heap (op : ValueOp) (rom : PhysicalROM)
    (bank : Register → Nat) (state : WordState bits) :
    (executeOps rom (op.lower bank) state).heap =
      Function.update state.heap (BitVec.ofNat bits (bank op.target))
        (op.value (bankRegisters bank state.heap)) := by
  change (executeOps rom (op.lower bank) state).heap =
    Function.update state.heap (BitVec.ofNat bits (bank op.target))
      (op.value (fun reg => state.heap (BitVec.ofNat bits (bank reg))))
  cases op <;>
    simp [ValueOp.lower, ValueOp.target, ValueOp.value,
      readBank, writeControl, executeOps, packingExecuteOp, wordOp, wordInstruction]

theorem valueOp_original_registers (op : ValueOp) (rom : PhysicalROM)
    (state : WordState bits) :
    (wordOp rom op.original state).register =
      Function.update state.register op.target (op.value state.register) := by
  cases op <;> rfl

/-- The executed finite literal code updates exactly the original virtual
register. Sources may alias each other or the destination. -/
theorem valueOp_lower_simulation (op : ValueOp) (rom : PhysicalROM)
    (bank : Register → Nat)
    (hi : Function.Injective (fun reg => BitVec.ofNat bits (bank reg)))
    (state : WordState bits) :
    bankRegisters bank (executeOps rom (op.lower bank) state).heap =
      (wordOp rom op.original { state with register := bankRegisters bank state.heap }).register := by
  rw [valueOp_lower_heap, bankRegisters_update bank hi, valueOp_original_registers]

theorem valueOp_lower_length (op : ValueOp) (bank : Register → Nat) :
    (op.lower bank).length ≤ 9 := by
  cases op <;> simp [ValueOp.lower, readBank, writeControl]

theorem valueOp_lower_straight (op : ValueOp) (bank : Register → Nat) :
    StraightProgram (op.lower bank) := by
  cases op <;> simp [ValueOp.lower, readBank, writeControl, StraightProgram, StraightOp]

private theorem single_heap_frame (rom : PhysicalROM) (op : PackingOp)
    (point : BitVec bits) (hf : ∀ state : WordState bits,
      (packingExecuteOp rom op state).heap point = state.heap point) :
    WordPrefixFrame rom [op] point := by
  intro state count
  cases count with
  | zero => rfl
  | succ count => simpa only [List.take_succ_cons, List.take_nil, executeOps] using hf state

theorem valueOp_lower_prefix_frame (op : ValueOp) (rom : PhysicalROM)
    (bank : Register → Nat) (point : BitVec bits)
    (hne : point ≠ BitVec.ofNat bits (bank op.target)) :
    WordPrefixFrame rom (op.lower bank) point := by
  have hw : WordPrefixFrame rom (writeControl (bank op.target)) point :=
    fun state count => writeControl_prefix_frame rom _ count state point hne
  cases op with
  | constant target value =>
    apply wordPrefixFrame_append
    · exact single_heap_frame rom _ point (fun _ => rfl)
    · exact hw
  | add target left right =>
    apply wordPrefixFrame_append
    · apply wordPrefixFrame_append
      · apply wordPrefixFrame_append
        · exact readBank_prefix_frame rom bank .old left point
        · exact readBank_prefix_frame rom bank .fresh right point
      · exact single_heap_frame rom _ point (fun _ => rfl)
    · exact hw
  | minimum target left right =>
    apply wordPrefixFrame_append
    · apply wordPrefixFrame_append
      · apply wordPrefixFrame_append
        · exact readBank_prefix_frame rom bank .old left point
        · exact readBank_prefix_frame rom bank .fresh right point
      · exact single_heap_frame rom _ point (fun _ => rfl)
    · exact hw
  | select target condition whenTrue whenFalse =>
    apply wordPrefixFrame_append
    · apply wordPrefixFrame_append
      · apply wordPrefixFrame_append
        · apply wordPrefixFrame_append
          · exact readBank_prefix_frame rom bank .flag condition point
          · exact readBank_prefix_frame rom bank .old whenTrue point
        · exact readBank_prefix_frame rom bank .fresh whenFalse point
      · exact single_heap_frame rom _ point (fun _ => rfl)
    · exact hw
  | subtract target left right =>
    apply wordPrefixFrame_append
    · apply wordPrefixFrame_append
      · apply wordPrefixFrame_append
        · exact readBank_prefix_frame rom bank .old left point
        · exact readBank_prefix_frame rom bank .fresh right point
      · exact single_heap_frame rom _ point (fun _ => rfl)
    · exact hw

end PaperProofs.Structure.LaminarTree.PSTRBuildLower
