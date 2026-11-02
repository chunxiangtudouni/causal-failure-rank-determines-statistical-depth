module
public import PaperProofs.Structure.PA17_QueryHeaderWord_022a

/-! Data-state and allocation transport for actual original RAM programs.
PC changes do not alter the register/heap computation; every actual access
is still checked separately. -/
@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA17DataFrame039

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

def DataEq (left right : State) : Prop := left.register = right.register ∧ left.heap = right.heap

theorem DataEq.refl (state : State) : DataEq state state := ⟨rfl, rfl⟩

theorem DataEq.symm {left right : State} (heq : DataEq left right) : DataEq right left :=
  ⟨heq.1.symm, heq.2.symm⟩

theorem op_dataEq (rom : ROM) (op : Op) (left right : State) (heq : DataEq left right) :
    DataEq (op.execute rom left) (op.execute rom right) := by
  rcases left with ⟨register, heap, pc⟩
  rcases right with ⟨otherRegister, otherHeap, otherPc⟩
  rcases heq with ⟨rfl, rfl⟩
  cases op with
  | subtract target first second => exact ⟨rfl, rfl⟩
  | base instruction => cases instruction <;> exact ⟨rfl, rfl⟩

theorem execute_dataEq (rom : ROM) (code : List Op) (left right : State) (heq : DataEq left right) :
    DataEq (execute rom code left) (execute rom code right) := by
  induction code generalizing left right with
  | nil => exact heq
  | cons op later ih => exact ih _ _ (op_dataEq rom op left right heq)

theorem accessFits_dataEq (rom : PhysicalROM) (heapWords : Nat) (op : Op)
    (left right : State) (heq : DataEq left right) :
    AccessFits rom heapWords left op ↔ AccessFits rom heapWords right op := by
  cases op with
  | subtract target first second => rfl
  | base instruction => cases instruction <;> simp only [AccessFits, heq.1]

theorem numericSafe_dataEq (B heapWords : Nat) (rom : PhysicalROM) (code : List Op)
    (left right : State) (heq : DataEq left right) (hs : NumericSafe B heapWords rom code left) :
    NumericSafe B heapWords rom code right := by
  constructor
  · intro count hc register
    have hh := execute_dataEq rom.semantic (code.take count) left right heq
    rw [← hh.1]
    exact hs.1 count hc register
  · intro count hc
    exact (accessFits_dataEq rom heapWords code[count] _ _
      (execute_dataEq rom.semantic (code.take count) left right heq)).mp (hs.2 count hc)

theorem capacityThroughout_dataEq (q capWords : Nat) (rom : PhysicalROM) (code : List Op)
    (left right : State) (heq : DataEq left right) (hs : CapacityThroughout q capWords rom code left) :
    CapacityThroughout q capWords rom code right := by
  intro count hc address ha
  rw [← (execute_dataEq rom.semantic (code.take count) left right heq).2]
  exact hs count hc address ha

theorem accessFits_mono (rom : PhysicalROM) (oldWords newWords : Nat) (hwords : oldWords ≤ newWords)
    (state : State) (op : Op) (hs : AccessFits rom oldWords state op) : AccessFits rom newWords state op := by
  cases op with
  | subtract target first second => trivial
  | base instruction =>
    cases instruction with
    | loadROM region target pointer => exact hs
    | loadHeap target pointer => exact lt_of_lt_of_le hs hwords
    | storeHeap pointer source => exact lt_of_lt_of_le hs hwords
    | constant target value => trivial
    | add target first second => trivial
    | minimum target first second => trivial
    | select target condition first second => trivial

theorem numericSafe_mono (B oldWords newWords : Nat) (hwords : oldWords ≤ newWords)
    (rom : PhysicalROM) (code : List Op) (state : State) (hs : NumericSafe B oldWords rom code state) :
    NumericSafe B newWords rom code state :=
  ⟨hs.1, fun count hc => accessFits_mono rom oldWords newWords hwords _ _ (hs.2 count hc)⟩

end PaperProofs.Structure.LaminarTree.PA17DataFrame039
