module

public import Structure.PSTR_BuildLower_SourceFacts_046

/-! Structural source-prefix contexts for AST/list induction. They only record
an exact split of the ORIGINAL buildProgram and the actual source state after
the consumed instructions. The proved whole-source invariants then apply to
each recursive body without a new safety or performance premise. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceContext
open IndexedRAM IndexedClosureRAM AlgorithmClaims

structure Context (q : Nat) (full : List (Finset (Fin q))) (code : List Op) (logical : State) where
  consumed : List Op
  remaining : List Op
  program_eq : SourceFacts.program q full = consumed ++ code ++ remaining
  state_eq : logical = IndexedClosureRAM.execute (givenTreeROM q full).semantic consumed (initial (fun _ => 0))

def start (q : Nat) (full : List (Finset (Fin q))) :
    Context q full (SourceFacts.program q full) (initial (fun _ => 0)) :=
  ⟨[], [], by simp, rfl⟩

def advance {q : Nat} {full : List (Finset (Fin q))} {op : Op} {later : List Op} {logical : State}
    (context : Context q full (op :: later) logical) :
    Context q full later (op.execute (givenTreeROM q full).semantic logical) :=
  { consumed := context.consumed ++ [op]
    remaining := context.remaining
    program_eq := by simpa only [List.append_assoc, List.singleton_append] using context.program_eq
    state_eq := by rw [IndexedClosureRAM.execute_append, ← context.state_eq]; rfl }

def left {q : Nat} {full : List (Finset (Fin q))} {first later : List Op} {logical : State}
    (context : Context q full (first ++ later) logical) : Context q full first logical :=
  { consumed := context.consumed
    remaining := later ++ context.remaining
    program_eq := by simpa only [List.append_assoc] using context.program_eq
    state_eq := context.state_eq }

def right {q : Nat} {full : List (Finset (Fin q))} {first later : List Op} {logical : State}
    (context : Context q full (first ++ later) logical) :
    Context q full later (IndexedClosureRAM.execute (givenTreeROM q full).semantic first logical) :=
  { consumed := context.consumed ++ first
    remaining := context.remaining
    program_eq := by simpa only [List.append_assoc] using context.program_eq
    state_eq := by rw [IndexedClosureRAM.execute_append, ← context.state_eq] }

theorem bound {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (count : Nat) (hc : count ≤ code.length) :
    context.consumed.length + count ≤ (SourceFacts.program q full).length := by
  rw [context.program_eq, List.length_append, List.length_append]
  omega

theorem index_bound {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (count : Nat) (hc : count < code.length) :
    context.consumed.length + count < (SourceFacts.program q full).length := by
  rw [context.program_eq, List.length_append, List.length_append]
  omega

theorem state_at {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (count : Nat) (hc : count ≤ code.length) :
    IndexedClosureRAM.execute (givenTreeROM q full).semantic (code.take count) logical =
      SourceFacts.before q full (context.consumed.length + count) := by
  have hcut : (SourceFacts.program q full).take (context.consumed.length + count) = context.consumed ++ code.take count := by
    rw [context.program_eq, List.append_assoc, List.take_append,
      List.take_of_length_le (by omega), Nat.add_sub_cancel_left, List.take_append_of_le_length hc]
  rw [SourceFacts.before, hcut, IndexedClosureRAM.execute_append]
  exact congrArg (IndexedClosureRAM.execute (givenTreeROM q full).semantic (code.take count)) context.state_eq

theorem instruction_at {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (count : Nat) (hc : count < code.length) :
    (SourceFacts.program q full)[context.consumed.length + count]'(index_bound context count hc) = code[count] := by
  simp only [context.program_eq, List.append_assoc, List.getElem_append_right (by omega :
    context.consumed.length ≤ context.consumed.length + count), Nat.add_sub_cancel_left,
    List.getElem_append_left hc]

theorem register_fits {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (hq : 0 < q) (hl : LaminarSchedule full)
    (count : Nat) (hc : count ≤ code.length) (reg : Register) :
    Fits (indexWidth 32 full.length q)
      ((IndexedClosureRAM.execute (givenTreeROM q full).semantic (code.take count) logical).register reg) := by
  rw [state_at context count hc]
  exact SourceFacts.register_fits q full hq hl _ (bound context count hc) reg

theorem capacity {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (hq : 0 < q) (hl : LaminarSchedule full)
    (count : Nat) (hc : count ≤ code.length) :
    CapacityPrefixBounded q (PA17CellLayout003.capacityWords full.length q (SourceFacts.size q full))
      (IndexedClosureRAM.execute (givenTreeROM q full).semantic (code.take count) logical).heap := by
  rw [state_at context count hc]
  exact SourceFacts.capacity q full hq hl _ (bound context count hc)

theorem access {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (hq : 0 < q) (hl : LaminarSchedule full)
    (count : Nat) (hc : count < code.length) :
    AccessFits (givenTreeROM q full) (PA17QueryLayout014.heapWords full.length q (SourceFacts.size q full))
      (IndexedClosureRAM.execute (givenTreeROM q full).semantic (code.take count) logical) code[count] := by
  rw [state_at context count hc.le, ← instruction_at context count hc]
  exact SourceFacts.access q full hq hl _ (index_bound context count hc)

theorem input_lower {q : Nat} {full : List (Finset (Fin q))} {code : List Op} {logical : State}
    (context : Context q full code logical) (count : Nat) (hc : count < code.length)
    (target pointer : Register) (hop : code[count] = .base (.loadROM .input target pointer)) :
    3 ≤ (IndexedClosureRAM.execute (givenTreeROM q full).semantic (code.take count) logical).register pointer := by
  rw [state_at context count hc.le]
  exact SourceFacts.input_lower q full _ (index_bound context count hc) target pointer
    ((instruction_at context count hc).trans hop)

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceContext
