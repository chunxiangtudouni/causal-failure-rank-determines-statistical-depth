module

public import PaperProofs.Structure.AlgorithmClaims

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryHeaderWord022

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def RegistersLE (bound : Nat) (state : State) : Prop := ∀ register, state.register register ≤ bound

def NumericSafe (bound heapWords : Nat) (rom : PhysicalROM) (ops : List Op) (state : State) : Prop :=
  (∀ count ≤ ops.length, RegistersLE bound (execute rom.semantic (ops.take count) state)) ∧
    ∀ count (hc : count < ops.length), AccessFits rom heapWords (execute rom.semantic (ops.take count) state) ops[count]

theorem NumericSafe.final (bound heapWords : Nat) (rom : PhysicalROM) (ops : List Op) (state : State)
    (hsafe : NumericSafe bound heapWords rom ops state) : RegistersLE bound (execute rom.semantic ops state) := by
  simpa only [List.take_length] using hsafe.1 ops.length le_rfl

theorem NumericSafe.append (bound heapWords : Nat) (rom : PhysicalROM) (left right : List Op) (state : State)
    (hl : NumericSafe bound heapWords rom left state)
    (hr : NumericSafe bound heapWords rom right (execute rom.semantic left state)) :
    NumericSafe bound heapWords rom (left ++ right) state := by
  constructor
  · intro count hc
    by_cases hs : count ≤ left.length
    · rw [List.take_append_of_le_length hs]
      exact hl.1 count hs
    · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
      rw [heq, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
        IndexedClosureRAM.execute_append]
      apply hr.1
      rw [List.length_append] at hc
      omega
  · intro count hc
    by_cases hs : count < left.length
    · rw [List.take_append_of_le_length hs.le, List.getElem_append_left hs]
      exact hl.2 count hs
    · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
      have he : extra < right.length := by rw [List.length_append] at hc; omega
      subst count
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
        IndexedClosureRAM.execute_append, List.getElem_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using hr.2 extra he

end PaperProofs.Structure.LaminarTree.PA17QueryHeaderWord022
