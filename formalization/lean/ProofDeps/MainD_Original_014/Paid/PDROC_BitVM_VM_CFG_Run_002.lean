module

public import Paid.PDROC_BitVM_VM_CFG_Run_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Run

open Turing PDROC.BitVM.Common.IO PaperProofs.Paid.Computation

variable {Λ σ : Type}

/-- Internal uniform local-cost interface. The parent proves this from
the real fixed FullCFG one-step theorem. Boundary is actual prefix proof
data, not a program field, extra paper input or numerical oracle. -/
def StepQ (native : Λ → TM2.Stmt Alphabet Λ σ) (code : Program) (input : List Cell)
    (states : List State) (entry : State → NativeState Λ σ → Prop) (Q : ℕ) : Prop :=
  ∀ (current next : State) (instruction : Instruction) (events : List Log.HeapEvent) (physical : NativeState Λ σ),
    Boundary code states current events → code[current.pc]? = some instruction →
    step code input current = some next → next.pc < code.size →
    Source.Ready input current events physical.stk → entry current physical →
    ∃ after : NativeState Λ σ, entry next after ∧
      Source.Ready input next (events ++ (Log.eventOf instruction current).toList) after.stk ∧
      ∃ path : ActualPath (TM2.step native) physical after, path.posts.length ≤ Q

def HaltQ (native : Λ → TM2.Stmt Alphabet Λ σ) (code : Program) (input : List Cell)
    (states : List State) (entry : State → NativeState Λ σ → Prop) (Q : ℕ) : Prop :=
  ∀ (current : State) (events : List Log.HeapEvent) (physical : NativeState Λ σ),
    Boundary code states current events → code[current.pc]? = some .halt →
    Source.Ready input current events physical.stk → entry current physical →
    ∃ after : NativeState Λ σ, TM2.step native after = none ∧
      Source.Ready input current events after.stk ∧
      ∃ path : ActualPath (TM2.step native) physical after, path.posts.length ≤ Q

/-- The complete original Runs is followed by one native ActualPath.
Entry and all local callback hypotheses are INTERNAL compiler obligations,
discharged later by actual opcode/cleaner/initial/terminal implementations.
The original state list, events and prefix induction stay only in proofs. -/
theorem runs_path_Q (native : Λ → TM2.Stmt Alphabet Λ σ) (code : Program) (input : List Cell)
    (states : List State) (final : State) (actual : Runs code input states final)
    (entry : State → NativeState Λ σ → Prop) (boot : NativeState Λ σ) (Q : ℕ)
    (simulate : StepQ native code input states entry Q) (finish : HaltQ native code input states entry Q)
    (startup : ∃ first : NativeState Λ σ, entry initial first ∧ Source.Ready input initial [] first.stk ∧
      ∃ path : ActualPath (TM2.step native) boot first, path.posts.length ≤ Q) :
    ∃ terminal : NativeState Λ σ, TM2.step native terminal = none ∧
      Source.Ready input final (BoundaryBudget.actualHistory code states) terminal.stk ∧
      ∃ path : ActualPath (TM2.step native) boot terminal, path.posts.length ≤ (states.length + 1) * Q := by
  cases states with
  | nil => cases actual.1
  | cons first sourceRest =>
    have firstEqual : first = initial := Option.some.inj actual.1
    subst first
    let whole := initial :: sourceRest
    have valid := Source.runs_pc_valid code input whole final actual
    have build : ∀ (later earlier : List State) (current : State) (physical : NativeState Λ σ),
        whole = earlier ++ current :: later →
        (current :: later).IsChain (fun a b => step code input a = some b) →
        (current :: later).getLast? = some final →
        Source.Ready input current (BoundaryBudget.actualHistory code (earlier ++ [current])) physical.stk →
        entry current physical →
        ∃ terminal : NativeState Λ σ, TM2.step native terminal = none ∧
          Source.Ready input final (BoundaryBudget.actualHistory code whole) terminal.stk ∧
          ∃ path : ActualPath (TM2.step native) physical terminal, path.posts.length ≤ (later.length + 1) * Q := by
      intro later
      induction later with
      | nil =>
        intro earlier current physical same chain last ready related
        have currentEqual : current = final := Option.some.inj last
        subst current
        have boundary : Boundary code whole final (BoundaryBudget.actualHistory code (earlier ++ [final])) :=
          ⟨earlier, [], same, rfl⟩
        obtain ⟨terminal, halted, represented, path, bounded⟩ :=
          finish final _ physical boundary actual.2.2.2.1 ready related
        refine ⟨terminal, halted, ?_, path, ?_⟩
        · simpa only [same] using represented
        · simpa only [List.length_nil, Nat.zero_add, Nat.one_mul] using bounded
      | cons next later ih =>
        intro earlier current physical same chain last ready related
        obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
        have tailLast : (next :: later).getLast? = some final := by
          simpa only [List.getLast?_cons_cons] using last
        obtain ⟨instruction, fetched, executed⟩ := Source.fetch_of_step code input current next edge
        have nextMember : next ∈ whole := by rw [same]; simp
        have boundary : Boundary code whole current (BoundaryBudget.actualHistory code (earlier ++ [current])) :=
          ⟨earlier, next :: later, same, rfl⟩
        obtain ⟨nextPhysical, nextRelated, nextReady, firstPath, firstTime⟩ :=
          simulate current next instruction _ physical boundary fetched edge (valid next nextMember) ready related
        have prefixLast : (earlier ++ [current]).getLast? = some current :=
          List.getLast?_append_cons earlier current []
        have history := BoundaryBudget.actualHistory_append code (earlier ++ [current]) current next prefixLast
        rw [step_events code current instruction fetched] at history
        have nextSame : whole = (earlier ++ [current]) ++ next :: later := by
          simpa only [List.append_assoc, List.singleton_append] using same
        have readyNext : Source.Ready input next
            (BoundaryBudget.actualHistory code ((earlier ++ [current]) ++ [next])) nextPhysical.stk := by
          rw [history]
          exact nextReady
        obtain ⟨terminal, halted, represented, laterPath, laterTime⟩ :=
          ih (earlier ++ [current]) next nextPhysical nextSame tailChain tailLast readyNext nextRelated
        refine ⟨terminal, halted, represented, firstPath.trans laterPath, ?_⟩
        change (firstPath.posts ++ laterPath.posts).length ≤ ((next :: later).length + 1) * Q
        simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
        simp only [Nat.add_mul, Nat.one_mul] at laterTime
        omega
    obtain ⟨atInitial, initialRelated, initialReady, initialPath, initialTime⟩ := startup
    have readyInitial : Source.Ready input initial
        (BoundaryBudget.actualHistory code ([] ++ [initial])) atInitial.stk := by
      simpa only [List.nil_append, BoundaryBudget.actualHistory, List.dropLast_singleton, List.flatMap_nil] using initialReady
    obtain ⟨terminal, halted, represented, bodyPath, bodyTime⟩ :=
      build sourceRest [] initial atInitial rfl actual.2.1 actual.2.2.1 readyInitial initialRelated
    refine ⟨terminal, halted, represented, initialPath.trans bodyPath, ?_⟩
    change (initialPath.posts ++ bodyPath.posts).length ≤ ((initial :: sourceRest).length + 1) * Q
    simp only [List.length_append, List.length_cons, Nat.add_mul, Nat.one_mul]
    simp only [Nat.add_mul, Nat.one_mul] at bodyTime
    omega

end PDROC.BitVM.VM.CFG.Run
