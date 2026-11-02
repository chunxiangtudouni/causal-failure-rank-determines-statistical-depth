module

public import Structure.PSTR_BuildLower_ASTExprBounds_035

/-! A proof-producing compile-time certificate for the ORIGINAL fixed AST:
every actual source .input load has pointer≥3. This closes the port's real
stage/node domain internally; no header-read restriction is a caller input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceInput
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17UniformGenerator035b PA17ProgramTemplates041

def lowerThree : Expr → Bool
  | .constant value => decide (3 ≤ value)
  | .binary .add left right => lowerThree left || lowerThree right
  | _ => false

theorem lowerThree_sound (expr : Expr) (rom : PhysicalROM) (environment : Nat → Nat)
    (hc : lowerThree expr = true) : 3 ≤ expr.eval rom environment := by
  induction expr with
  | constant value => exact of_decide_eq_true hc
  | cell address => simp [lowerThree] at hc
  | input address => simp [lowerThree] at hc
  | binary operation left right ihl ihr =>
    cases operation with
    | add =>
      rcases Bool.or_eq_true_iff.mp hc with hl | hr
      · have hh := ihl hl
        change 3 ≤ left.eval rom environment + right.eval rom environment
        omega
      · have hh := ihr hr
        change 3 ≤ left.eval rom environment + right.eval rom environment
        omega
    | subtract | minimum | multiply | divide | bitAnd | bitOr | shiftLeft | shiftRight => simp [lowerThree] at hc

def isInputRead : OpExpr → Bool
  | .literal (.base (.loadROM .input _ _)) => true
  | _ => false

inductive Guarded : List OpExpr → Prop where
  | nil : Guarded []
  | plain (first : OpExpr) (later : List OpExpr) (hn : isInputRead first = false)
      (rest : Guarded later) : Guarded (first :: later)
  | pair (pointer : Register) (expr : Expr) (target : Register) (later : List OpExpr)
      (bound : lowerThree expr = true) (rest : Guarded later) :
      Guarded (.constant pointer expr :: .literal (.base (.loadROM .input target pointer)) :: later)

/-- This returns a proof object, never an unchecked mathematical answer. -/
def checkCode : (ops : List OpExpr) → Option (PLift (Guarded ops))
  | [] => some ⟨.nil⟩
  | .constant pointer expr :: .literal (.base (.loadROM .input target other)) :: later =>
    if same : other = pointer then
      if bound : lowerThree expr = true then
        (checkCode later).map (fun rest => ⟨by cases same; exact Guarded.pair pointer expr target later bound rest.down⟩)
      else none
    else none
  | first :: later =>
    if plain : isInputRead first = false then
      (checkCode later).map (fun rest => ⟨Guarded.plain first later plain rest.down⟩)
    else none

def ProgramGuarded : Program → Prop
  | .code ops => Guarded ops
  | .append left right => ProgramGuarded left ∧ ProgramGuarded right
  | .repeat _ _ body => ProgramGuarded body

def checkProgram : (program : Program) → Option (PLift (ProgramGuarded program))
  | .code ops => checkCode ops
  | .append left right => do
      let hl ← checkProgram left
      let hr ← checkProgram right
      pure ⟨⟨hl.down, hr.down⟩⟩
  | .repeat _ _ body => checkProgram body

theorem fullBuild_guarded : ProgramGuarded fullBuild := by
  have checked : (checkProgram fullBuild).isSome = true := by decide
  cases hh : checkProgram fullBuild with
  | none => simp [hh] at checked
  | some proof => exact proof.down

def stepLower (op : Op) (state : State) : Prop :=
  match op with
  | .base (.loadROM .input _ pointer) => 3 ≤ state.register pointer
  | _ => True

def Throughout (rom : PhysicalROM) (program : List Op) : Prop :=
  ∀ (state : State) count (hc : count < program.length),
    stepLower program[count] (IndexedClosureRAM.execute rom.semantic (program.take count) state)

private theorem plain_lower (op : OpExpr) (dimensions : PhysicalROM) (environment : Nat → Nat)
    (state : State) (hn : isInputRead op = false) : stepLower (op.eval dimensions environment) state := by
  cases op with
  | constant target expr => trivial
  | literal original =>
    cases original with
    | subtract target left right => trivial
    | base instruction =>
      cases instruction <;> try trivial
      case loadROM region target pointer =>
        cases region with
        | input => simp [isInputRead] at hn
        | internal => trivial
        | children => trivial

private theorem plain_cons (rom : PhysicalROM) (first : Op) (later : List Op)
    (head : ∀ state, stepLower first state) (rest : Throughout rom later) : Throughout rom (first :: later) := by
  intro state count hc
  cases count with
  | zero => exact head state
  | succ count =>
    have hr : count < later.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hc
    exact rest (first.execute rom.semantic state) count hr

private theorem pair_cons (rom : PhysicalROM) (pointer : Register) (value : Nat) (target : Register) (later : List Op)
    (hv : 3 ≤ value) (rest : Throughout rom later) :
    Throughout rom (.base (.constant pointer value) :: .base (.loadROM .input target pointer) :: later) := by
  intro state count hc
  cases count with
  | zero => trivial
  | succ count => cases count with
    | zero =>
      change 3 ≤ ((Op.base (.constant pointer value)).execute rom.semantic state).register pointer
      simpa only [Op.execute, Instruction.execute, Function.update_self] using hv
    | succ count =>
      have hr : count < later.length := by
        simp only [List.length_cons] at hc
        omega
      exact rest ((Op.base (.loadROM .input target pointer)).execute rom.semantic
        ((Op.base (.constant pointer value)).execute rom.semantic state)) count hr

theorem guarded_sound (ops : List OpExpr) (hc : Guarded ops) (dimensions rom : PhysicalROM)
    (environment : Nat → Nat) : Throughout rom (instructions dimensions environment ops) := by
  induction hc with
  | nil => intro state count h; simp [instructions] at h
  | plain first later hn _ ih =>
    exact plain_cons rom (first.eval dimensions environment) _
      (fun state => plain_lower first dimensions environment state hn) ih
  | pair pointer expr target later hb _ ih =>
    exact pair_cons rom pointer (expr.eval dimensions environment) target _
      (lowerThree_sound expr dimensions environment hb) ih

private theorem throughout_append (rom : PhysicalROM) (left right : List Op)
    (hl : Throughout rom left) (hr : Throughout rom right) : Throughout rom (left ++ right) := by
  intro state count hc
  by_cases hs : count < left.length
  · rw [List.take_append_of_le_length hs.le, List.getElem_append_left hs]
    exact hl state count hs
  · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (show left.length ≤ count by omega)
    have he : extra < right.length := by rw [List.length_append] at hc; omega
    rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
      IndexedClosureRAM.execute_append, List.getElem_append_right (by omega)]
    simpa only [Nat.add_sub_cancel_left] using hr (IndexedClosureRAM.execute rom.semantic left state) extra he

private theorem throughout_flatMap {α : Type*} (rom : PhysicalROM) (entries : List α) (block : α → List Op)
    (hb : ∀ entry ∈ entries, Throughout rom (block entry)) : Throughout rom (entries.flatMap block) := by
  induction entries with
  | nil => intro state count h; simp at h
  | cons entry later ih =>
    apply throughout_append rom (block entry) (later.flatMap block) (hb entry List.mem_cons_self)
    exact ih (fun other hm => hb other (List.mem_cons_of_mem _ hm))

theorem program_guarded_sound (program : Program) (hc : ProgramGuarded program) (dimensions rom : PhysicalROM)
    (environment : Nat → Nat) : Throughout rom (program.eval dimensions environment) := by
  induction program generalizing environment with
  | code ops => exact guarded_sound ops hc dimensions rom environment
  | append left right ihl ihr =>
    apply throughout_append
    · apply ihl
      exact hc.1
    · apply ihr
      exact hc.2
  | «repeat» counter bound body ih =>
    apply throughout_flatMap
    intro index _
    apply ih
    exact hc

theorem fullBuild_input_lower (N q t : Nat) (environment : Nat → Nat) (rom : PhysicalROM) :
    Throughout rom (PA17TableBuild005.buildProgram N q t) := by
  rw [← fullBuild_eval N q t environment]
  exact program_guarded_sound fullBuild fullBuild_guarded (dimensionROM N q t) rom environment

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.SourceInput
