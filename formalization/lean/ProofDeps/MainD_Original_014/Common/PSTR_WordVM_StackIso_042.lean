module

public import Common.PSTR_WordVM_LabelMap_029
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

/-! Static renaming of fixed Bool-stack roles. This is a code/configuration
isomorphism, not a runtime swap or a free physical data movement. The
consumer must establish the renamed actual physical entry. Every actual
step, internal node and stack length is transported on the same path. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.StackIso

open Turing
open scoped BigOperators

variable {K Λ σ : Type*}
abbrev Alphabet (_ : K) := Bool

def slots (roles : K ≃ K) (before : K → List Bool) : K → List Bool :=
  fun point => before (roles.symm point)

theorem slots_at (roles : K ≃ K) (before : K → List Bool) (point : K) :
    slots roles before (roles point) = before point := by simp only [slots, Equiv.symm_apply_apply]

def statement (roles : K ≃ K) : TM2.Stmt (Alphabet (K := K)) Λ σ → TM2.Stmt (Alphabet (K := K)) Λ σ
  | .push point value tail => .push (roles point) value (statement roles tail)
  | .peek point value tail => .peek (roles point) value (statement roles tail)
  | .pop point value tail => .pop (roles point) value (statement roles tail)
  | .load value tail => .load value (statement roles tail)
  | .branch test yes no => .branch test (statement roles yes) (statement roles no)
  | .goto target => .goto target
  | .halt => .halt

def configuration (roles : K ≃ K) (before : TM2.Cfg (Alphabet (K := K)) Λ σ) :
    TM2.Cfg (Alphabet (K := K)) Λ σ := ⟨before.l, before.var, slots roles before.stk⟩

theorem statement_actions (roles : K ≃ K) (body : TM2.Stmt (Alphabet (K := K)) Λ σ) :
    PSTRWordBool.ScannerClock.actions (statement roles body) = PSTRWordBool.ScannerClock.actions body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih => exact congrArg (· + 1) ih
  | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact congrArg₂ max yes no
  | goto _ => rfl
  | halt => rfl

theorem statement_pushes (roles : K ≃ K) (body : TM2.Stmt (Alphabet (K := K)) Λ σ) :
    PSTRWordBool.AuxWorkspace.pushes (statement roles body) = PSTRWordBool.AuxWorkspace.pushes body := by
  induction body with
  | push _ _ _ ih => exact congrArg (· + 1) ih
  | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact congrArg₂ max yes no
  | goto _ => rfl
  | halt => rfl

theorem statement_supports (roles : K ≃ K) (body : TM2.Stmt (Alphabet (K := K)) Λ σ) (support : Finset Λ) :
    TM2.SupportsStmt support (statement roles body) ↔ TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact and_congr yes no
  | goto _ => rfl
  | halt => rfl

theorem occupied_sum [Fintype K] (roles : K ≃ K) (before : K → List Bool) :
    (∑ point, (slots roles before point).length) = ∑ point, (before point).length :=
  roles.symm.sum_comp (fun point => (before point).length)

/-- Only writes are restricted; reading another stack does not alter it. -/
def WritesOnly (allowed : K → Prop) : TM2.Stmt (Alphabet (K := K)) Λ σ → Prop
  | .push point _ tail => allowed point ∧ WritesOnly allowed tail
  | .pop point _ tail => allowed point ∧ WritesOnly allowed tail
  | .peek _ _ tail | .load _ tail => WritesOnly allowed tail
  | .branch _ yes no => WritesOnly allowed yes ∧ WritesOnly allowed no
  | .goto _ | .halt => True

theorem writes_labelMap {Ω : Type*} (mapping : Λ → Ω) (allowed : K → Prop)
    (body : TM2.Stmt (Alphabet (K := K)) Λ σ) :
    WritesOnly allowed (LabelMap.statement mapping body) ↔ WritesOnly allowed body := by
  induction body with
  | push point value tail ih | pop point value tail ih => exact and_congr Iff.rfl ih
  | peek point value tail ih => exact ih
  | load value tail ih => exact ih
  | branch test yes no ihYes ihNo => exact and_congr ihYes ihNo
  | goto _ => rfl
  | halt => rfl

section Execution
variable [DecidableEq K]

theorem slots_update (roles : K ≃ K) (before : K → List Bool) (point : K) (value : List Bool) :
    slots roles (Function.update before point value) =
      Function.update (slots roles before) (roles point) value := by
  funext other
  by_cases same : other = roles point
  · subst other
    simp only [slots, Equiv.symm_apply_apply, Function.update_self]
  · have different : roles.symm other ≠ point := by
      intro equal
      apply same
      rw [← equal, Equiv.apply_symm_apply]
    simp only [slots, Function.update_of_ne different, Function.update_of_ne same]

theorem nodes_frame (allowed : K → Prop) (body : TM2.Stmt (Alphabet (K := K)) Λ σ)
    (writes : WritesOnly allowed body) (memory : σ) (before : K → List Bool)
    (point : K) (untouched : ¬allowed point) :
    ∀ node ∈ PSTRWordBool.AuxWorkspace.nodes body memory before, node.2 point = before point := by
  revert writes
  induction body generalizing memory before with
  | push target value tail ih =>
    intro writes
    have different : point ≠ target := by intro same; subst point; exact untouched writes.1
    intro node present
    rcases List.mem_cons.mp present with first | later
    · subst node
      rfl
    · exact (ih memory (Function.update before target (value memory :: before target)) writes.2 node later).trans
        (by simp only [Function.update_of_ne different])
  | pop target value tail ih =>
    intro writes
    have different : point ≠ target := by intro same; subst point; exact untouched writes.1
    intro node present
    rcases List.mem_cons.mp present with first | later
    · subst node
      rfl
    · exact (ih (value memory (before target).head?) (Function.update before target (before target).tail) writes.2 node later).trans
        (by simp only [Function.update_of_ne different])
  | peek target value tail ih =>
    intro writes node present
    rcases List.mem_cons.mp present with first | later
    · subst node
      rfl
    · exact ih (value memory (before target).head?) before writes node later
  | load value tail ih =>
    intro writes node present
    rcases List.mem_cons.mp present with first | later
    · subst node
      rfl
    · exact ih (value memory) before writes node later
  | branch test yes no ihYes ihNo =>
    intro writes node present
    cases choice : test memory
    · simp only [PSTRWordBool.AuxWorkspace.nodes, choice, Bool.false_eq_true, ite_false, List.mem_cons] at present
      rcases present with first | later
      · subst node
        rfl
      · exact ihNo memory before writes.2 node later
    · simp only [PSTRWordBool.AuxWorkspace.nodes, choice, ite_true, List.mem_cons] at present
      rcases present with first | later
      · subst node
        rfl
      · exact ihYes memory before writes.1 node later
  | goto _ | halt =>
    intro writes node present
    have same := List.mem_singleton.mp present
    subst node
    rfl

theorem stepAux_configuration (roles : K ≃ K) (body : TM2.Stmt (Alphabet (K := K)) Λ σ)
    (memory : σ) (before : K → List Bool) :
    TM2.stepAux (statement roles body) memory (slots roles before) =
      configuration roles (TM2.stepAux body memory before) := by
  induction body generalizing memory before with
  | push point value tail ih =>
    simp only [statement, TM2.stepAux, slots_at]
    rw [← slots_update]
    exact ih memory (Function.update before point (value memory :: before point))
  | peek point value tail ih =>
    simp only [statement, TM2.stepAux, slots_at]
    exact ih (value memory (before point).head?) before
  | pop point value tail ih =>
    simp only [statement, TM2.stepAux, slots_at]
    rw [← slots_update]
    exact ih (value memory (before point).head?) (Function.update before point (before point).tail)
  | load value tail ih => exact ih (value memory) before
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_false] using ihNo memory before
    · simpa only [statement, TM2.stepAux, choice, Bool.cond_true] using ihYes memory before
  | goto target => rfl
  | halt => rfl

theorem step_configuration_on (roles : K ≃ K) (source target : Λ → TM2.Stmt (Alphabet (K := K)) Λ σ)
    (before : TM2.Cfg (Alphabet (K := K)) Λ σ)
    (same : ∀ point, before.l = some point → target point = statement roles (source point)) :
    TM2.step target (configuration roles before) =
      (TM2.step source before).map (configuration roles) := by
  cases before with
  | mk position memory before =>
    cases position with
    | none => rfl
    | some point =>
      change some (TM2.stepAux (target point) memory (slots roles before)) = _
      rw [same point rfl, stepAux_configuration]
      rfl

theorem chain_configuration_on (roles : K ≃ K) (source target : Λ → TM2.Stmt (Alphabet (K := K)) Λ σ)
    (trace : List (TM2.Cfg (Alphabet (K := K)) Λ σ))
    (chain : trace.IsChain (fun before after => TM2.step source before = some after))
    (same : ∀ before ∈ trace.dropLast, ∀ point, before.l = some point → target point = statement roles (source point)) :
    (trace.map (configuration roles)).IsChain (fun before after => TM2.step target before = some after) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next rest =>
      obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
      have firstSame : ∀ point, first.l = some point → target point = statement roles (source point) := by
        intro point active
        exact same first (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) point active
      have tailSame : ∀ before ∈ (next :: rest).dropLast, ∀ point,
          before.l = some point → target point = statement roles (source point) := by
        intro before present point active
        apply same before _ point active
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present
      apply List.isChain_cons_cons.mpr
      refine ⟨?_, ih tailChain tailSame⟩
      rw [step_configuration_on roles source target first firstSame, edge, Option.map_some]

theorem nodes_statement (roles : K ≃ K) (body : TM2.Stmt (Alphabet (K := K)) Λ σ)
    (memory : σ) (before : K → List Bool) :
    PSTRWordBool.AuxWorkspace.nodes (statement roles body) memory (slots roles before) =
      (PSTRWordBool.AuxWorkspace.nodes body memory before).map (fun node => (node.1, slots roles node.2)) := by
  induction body generalizing memory before with
  | push point value tail ih =>
    simp only [statement, PSTRWordBool.AuxWorkspace.nodes, slots_at, List.map_cons]
    rw [← slots_update]
    exact congrArg (List.cons (memory, slots roles before))
      (ih memory (Function.update before point (value memory :: before point)))
  | peek point value tail ih =>
    simp only [statement, PSTRWordBool.AuxWorkspace.nodes, slots_at, List.map_cons]
    exact congrArg (List.cons (memory, slots roles before)) (ih (value memory (before point).head?) before)
  | pop point value tail ih =>
    simp only [statement, PSTRWordBool.AuxWorkspace.nodes, slots_at, List.map_cons]
    rw [← slots_update]
    exact congrArg (List.cons (memory, slots roles before))
      (ih (value memory (before point).head?) (Function.update before point (before point).tail))
  | load value tail ih =>
    exact congrArg (List.cons (memory, slots roles before)) (ih (value memory) before)
  | branch test yes no ihYes ihNo =>
    cases choice : test memory
    · simpa only [statement, PSTRWordBool.AuxWorkspace.nodes, choice, Bool.false_eq_true, ite_false, List.map_cons] using
        congrArg (List.cons (memory, slots roles before)) (ihNo memory before)
    · simpa only [statement, PSTRWordBool.AuxWorkspace.nodes, choice, ite_true, List.map_cons] using
        congrArg (List.cons (memory, slots roles before)) (ihYes memory before)
  | goto target => rfl
  | halt => rfl

end Execution
end PaperProofs.Common.Native.PSTRWordVM.StackIso
