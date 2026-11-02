module

public import PaperProofs.Structure.PA17_UniformGenerator_035d

/-! Runtime clock and state invariants for the actual finite-template
compiler. No generated target list is read by the program. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17UniformGenerator035e

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  PA17UniformGenerator035a PA17UniformGenerator035b PA17UniformGenerator035c PA17UniformGenerator035d

def clock (rom : PhysicalROM) (environment : Nat → Nat) (stack : Nat) : Template → Nat
  | .empty => 0
  | .word expression => (expression.compile stack).length + 8
  | .append left right => clock rom environment stack left + clock rom environment stack right
  | .repeat counter bound body =>
      (bound.compile stack).length + 2 +
        ((List.range (bound.eval rom environment)).reverse.map (fun index =>
          clock rom (Function.update environment counter (index + 1)) stack body + 12)).sum + 4

def loopWords (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (body : Template) (count : Nat) : List Nat :=
  (List.range count).reverse.flatMap (fun index => body.denote rom (Function.update environment counter (index + 1)))

def loopClock (rom : PhysicalROM) (environment : Nat → Nat) (stack counter : Nat) (body : Template) (count : Nat) : Nat :=
  ((List.range count).reverse.map (fun index => clock rom (Function.update environment counter (index + 1)) stack body + 12)).sum + 4

theorem loopWords_zero (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (body : Template) :
    loopWords rom environment counter body 0 = [] := rfl

theorem loopWords_succ (rom : PhysicalROM) (environment : Nat → Nat) (counter : Nat) (body : Template) (count : Nat) :
    loopWords rom environment counter body (count + 1) =
      body.denote rom (Function.update environment counter (count + 1)) ++ loopWords rom environment counter body count := by
  simp only [loopWords, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.flatMap_cons]

theorem loopClock_zero (rom : PhysicalROM) (environment : Nat → Nat) (stack counter : Nat) (body : Template) :
    loopClock rom environment stack counter body 0 = 4 := rfl

theorem loopClock_succ (rom : PhysicalROM) (environment : Nat → Nat) (stack counter : Nat) (body : Template) (count : Nat) :
    loopClock rom environment stack counter body (count + 1) =
      4 + clock rom (Function.update environment counter (count + 1)) stack body + 8 +
        loopClock rom environment stack counter body count := by
  simp only [loopClock, List.range_succ, List.reverse_append, List.reverse_singleton, List.singleton_append, List.map_cons, List.sum_cons]
  omega

def EnvRep (scope : Finset Nat) (environment heap : Nat → Nat) : Prop :=
  ∀ address ∈ scope, heap address = environment address

def ScopeBelow (stack : Nat) (scope : Finset Nat) : Prop :=
  ∀ address ∈ scope, address < stack

def CountersAvoid (cursor : Nat) : Template → Prop
  | .empty | .word _ => True
  | .append left right => CountersAvoid cursor left ∧ CountersAvoid cursor right
  | .repeat counter _ body => counter ≠ cursor ∧ CountersAvoid cursor body

theorem clock_scoped (template : Template) (rom : PhysicalROM) (stack : Nat) (scope : Finset Nat)
    (hs : template.WellScoped scope) (environment environment' : Nat → Nat)
    (he : EnvRep scope environment environment') :
    clock rom environment' stack template = clock rom environment stack template := by
  induction template generalizing scope environment environment' with
  | empty => rfl
  | word expression => rfl
  | append left right ihl ihr =>
    simp only [clock, ihl scope hs.1 environment environment' he, ihr scope hs.2 environment environment' he]
  | «repeat» counter bound body ih =>
    simp only [clock]
    rw [Expr.eval_cells_congr bound rom scope hs.2.1 environment environment' he]
    have hf : (fun index => clock rom (Function.update environment' counter (index + 1)) stack body + 12) =
        (fun index => clock rom (Function.update environment counter (index + 1)) stack body + 12) := by
      funext index
      rw [ih (insert counter scope) hs.2.2 (Function.update environment counter (index + 1))
        (Function.update environment' counter (index + 1))]
      intro address ha
      by_cases hz : address = counter
      · subst address
        simp only [Function.update_self]
      · simp only [Function.update_of_ne hz]
        exact he address ((Finset.mem_insert.mp ha).resolve_left hz)
    rw [hf]

theorem bind_noJump (expression : Expr) (stack target : Nat) : ∀ op ∈ bind expression stack target, NoJump op := by
  intro op hm
  rw [PA17UniformGenerator035d.bind, List.mem_append] at hm
  rcases hm with hm | hm
  · exact expression.compile_noJump stack op hm
  · have hh : ∀ entry ∈ spill target, NoJump entry := by simp [spill, NoJump]
    exact hh op hm

theorem bind_length (expression : Expr) (stack target : Nat) :
    (bind expression stack target).length = (expression.compile stack).length + 2 := by
  simp only [PA17UniformGenerator035d.bind, List.length_append, spill, List.length_cons, List.length_nil]

theorem bind_heap (expression : Expr) (rom : PhysicalROM) (stack target : Nat)
    (he : expression.Below stack) (state : NatState) :
    (runOps rom (bind expression stack target) state).heap =
      Function.update (runOps rom (expression.compile stack) state).heap target (expression.eval rom state.heap) := by
  rw [PA17UniformGenerator035d.bind, runOps_append, spill_heap, (expression.compile_correct rom stack he state).1]

theorem bind_target (expression : Expr) (rom : PhysicalROM) (stack target : Nat)
    (he : expression.Below stack) (state : NatState) :
    (runOps rom (bind expression stack target) state).heap target = expression.eval rom state.heap := by
  rw [bind_heap expression rom stack target he state, Function.update_self]

theorem bind_frame (expression : Expr) (rom : PhysicalROM) (stack target address : Nat)
    (he : expression.Below stack) (ht : address ≠ target)
    (hf : address < stack ∨ stack + expression.size ≤ address) (state : NatState) :
    (runOps rom (bind expression stack target) state).heap address = state.heap address := by
  rw [bind_heap expression rom stack target he state, Function.update_of_ne ht]
  exact expression_frame expression rom stack address hf state

theorem bind_env (expression : Expr) (rom : PhysicalROM) (stack target : Nat)
    (he : expression.Below stack) (scope : Finset Nat) (hb : ScopeBelow stack scope) (ht : target ∉ scope)
    (environment : Nat → Nat) (state : NatState) (hr : EnvRep scope environment state.heap) :
    EnvRep scope environment (runOps rom (bind expression stack target) state).heap := by
  intro address ha
  rw [bind_frame expression rom stack target address he (by intro hz; subst address; exact ht ha) (Or.inl (hb address ha)) state]
  exact hr address ha

theorem bind_stream (expression : Expr) (rom : PhysicalROM) (stack target cursor outputBase : Nat)
    (he : expression.Below stack) (ht : target < stack) (hc : cursor < stack) (hne : cursor ≠ target)
    (hs : stack + expression.size ≤ outputBase) (words : List Nat) (state : NatState)
    (hr : StreamRep cursor outputBase words state.heap) :
    StreamRep cursor outputBase words (runOps rom (bind expression stack target) state).heap := by
  constructor
  · rw [bind_frame expression rom stack target cursor he hne (Or.inl hc) state]
    exact hr.1
  · intro position hp
    rw [bind_frame expression rom stack target (outputBase + position) he (by omega) (Or.inr (by omega)) state]
    exact hr.2 position hp

theorem emitWord_env (expression : Expr) (rom : PhysicalROM) (stack cursor outputBase : Nat)
    (he : expression.Below stack) (hc : cursor < stack) (hs : stack + expression.size ≤ outputBase)
    (scope : Finset Nat) (hb : ScopeBelow stack scope) (hcursor : cursor ∉ scope)
    (environment : Nat → Nat) (state : NatState) (hr : EnvRep scope environment state.heap) :
    EnvRep scope environment (runOps rom (emitWord expression stack cursor outputBase) state).heap := by
  intro address ha
  rw [emitWord_counter_frame expression rom stack cursor outputBase address he hc (hb address ha)
    (by intro hz; subst address; exact hcursor ha) hs state]
  exact hr address ha

end PaperProofs.Structure.LaminarTree.PA17UniformGenerator035e
