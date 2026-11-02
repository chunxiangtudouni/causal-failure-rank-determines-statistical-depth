module

public import Paid.PDROC_BitVM_Codec_FieldOps_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.FieldOps

open Turing PDROC.BitVM.Native

structure Path {Λ σ : Type} (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (before after : TM2.Cfg Alphabet Λ σ) where
  states : List (TM2.Cfg Alphabet Λ σ)
  first : states.head? = some before
  actual : states.IsChain (fun a b => TM2.step machine a = some b)
  last : states.getLast? = some after

theorem joined_last {α : Type} (left right : List α) (middle after : α)
    (leftLast : left.getLast? = some middle) (rightHead : right.head? = some middle)
    (rightLast : right.getLast? = some after) : (left ++ right.tail).getLast? = some after := by
  cases right with
  | nil => simp only [List.head?_nil, reduceCtorEq] at rightHead
  | cons head tail =>
    cases tail with
    | nil =>
      have start : head = middle := Option.some.inj rightHead
      have finish : head = after := Option.some.inj rightLast
      simp only [List.tail_cons, List.append_nil]
      exact leftLast.trans (congrArg some (start.symm.trans finish))
    | cons next rest =>
      have notOne : (head :: next :: rest).length ≠ 1 := by
        simp only [List.length_cons]
        omega
      simp only [List.getLast?_append, List.getLast?_tail, notOne, ↓reduceIte,
        rightLast, Option.some_or]

def Path.append {Λ σ : Type} {machine : Λ → TM2.Stmt Alphabet Λ σ}
    {before middle after : TM2.Cfg Alphabet Λ σ}
    (left : Path machine before middle) (right : Path machine middle after) : Path machine before after where
  states := left.states ++ right.states.tail
  first := by simp only [List.head?_append, left.first, Option.some_or]
  actual := PDROC.BitVM.Log.TwoStack.join_chain left.states right.states middle
    left.actual right.actual left.last right.first
  last := joined_last left.states right.states middle after left.last right.first right.last

theorem Path.append_length {Λ σ : Type} {machine : Λ → TM2.Stmt Alphabet Λ σ}
    {before middle after : TM2.Cfg Alphabet Λ σ}
    (left : Path machine before middle) (right : Path machine middle after) :
    (left.append right).states.length ≤ left.states.length + right.states.length := by
  simp only [Path.append, List.length_append, List.length_tail]
  omega

def Path.single {Λ σ : Type} {machine : Λ → TM2.Stmt Alphabet Λ σ}
    {before after : TM2.Cfg Alphabet Λ σ} (edge : TM2.step machine before = some after) : Path machine before after :=
  ⟨[before, after], rfl, List.isChain_cons_cons.mpr ⟨edge, List.isChain_singleton _⟩, rfl⟩

/-- This is a proof transport of actual edges, not a new transition. Every
use below instantiates transform/edge with already-proved literal adapters. -/
def Path.transport {Λ Ω σ υ : Type}
    {source : Λ → TM2.Stmt Alphabet Λ σ} {caller : Ω → TM2.Stmt Alphabet Ω υ}
    {before after : TM2.Cfg Alphabet Λ σ} (path : Path source before after)
    (transform : TM2.Cfg Alphabet Λ σ → TM2.Cfg Alphabet Ω υ)
    (edge : ∀ a b, TM2.step source a = some b → TM2.step caller (transform a) = some (transform b)) :
    Path caller (transform before) (transform after) where
  states := path.states.map transform
  first := by simp only [List.head?_map, path.first, Option.map_some]
  actual := List.isChain_map_of_isChain _ edge path.actual
  last := by simp only [List.getLast?_map, path.last, Option.map_some]

theorem Path.transport_length {Λ Ω σ υ : Type}
    {source : Λ → TM2.Stmt Alphabet Λ σ} {caller : Ω → TM2.Stmt Alphabet Ω υ}
    {before after : TM2.Cfg Alphabet Λ σ} (path : Path source before after)
    (transform : TM2.Cfg Alphabet Λ σ → TM2.Cfg Alphabet Ω υ)
    (edge : ∀ a b, TM2.step source a = some b → TM2.step caller (transform a) = some (transform b)) :
    (path.transport transform edge).states.length = path.states.length := List.length_map _

/-- Actual finite-store reordering of an Inline call, including the real
return jump which replaces its source HALT. All four types are fixed finite
types in the constructed machines; no numerical datum is added to control. -/
theorem iso_inline_edge {Λ Ω σ τ υ : Type} (iso : (σ × τ) ≃ υ)
    (labels : Λ → Ω) (finish : Ω) (extra : τ)
    (source : Λ → TM2.Stmt Alphabet Λ σ) (caller : Ω → TM2.Stmt Alphabet Ω υ)
    (agrees : ∀ label, caller (labels label) =
      StoreIso.statement iso (Inline.statement labels finish (source label)))
    (before after : TM2.Cfg Alphabet Λ σ) (edge : TM2.step source before = some after) :
    TM2.step caller (StoreIso.cfg iso (Inline.cfg labels finish extra before)) =
      some (StoreIso.cfg iso (Inline.cfg labels finish extra after)) := by
  rcases before with ⟨label, saved, contents⟩
  cases label with
  | none => cases edge
  | some label =>
    have actual : TM2.stepAux (source label) saved contents = after := Option.some.inj edge
    change some (TM2.stepAux (caller (labels label)) (iso (saved, extra)) contents) = _
    rw [agrees, StoreIso.stepAux_map, Inline.stepAux_map, actual]

/-- The existing genuine Lift.path on one three-role callee, with a fully
specified final caller array. Selection and outside equations are verified
from real produced bytes by each macro call, never given to outer runs. -/
theorem lift_three {Λ σ : Type} (embed : Fin 3 ↪ Stack)
    (source : Λ → TM2.Stmt (fun _ : Fin 3 => Bool) Λ σ)
    (localBefore localAfter : TM2.Cfg (fun _ : Fin 3 => Bool) Λ σ)
    (run : List (TM2.Cfg (fun _ : Fin 3 => Bool) Λ σ))
    (head : run.head? = some localBefore)
    (chain : run.IsChain (fun a b => TM2.step source a = some b))
    (last : run.getLast? = some localAfter)
    (contents finalContents : Stack → List Bool)
    (beforeData : Lift.slots embed contents = localBefore.stk)
    (afterData : Lift.slots embed finalContents = localAfter.stk)
    (outside : ∀ other, (∀ role, other ≠ embed role) → finalContents other = contents other) :
    ∃ path : Path (Lift.machine embed source)
      (⟨localBefore.l, localBefore.var, contents⟩ : TM2.Cfg Alphabet Λ σ)
      (⟨localAfter.l, localAfter.var, finalContents⟩ : TM2.Cfg Alphabet Λ σ),
      path.states.length = run.length := by
  cases run with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons first rest =>
    have same : first = localBefore := Option.some.inj head
    subst first
    let rawBefore : TM2.Cfg Alphabet Λ σ := ⟨localBefore.l, localBefore.var, contents⟩
    have initial : Lift.cfg embed rawBefore = localBefore := by
      rcases localBefore with ⟨label, saved, data⟩
      change Lift.slots embed contents = data at beforeData
      change (⟨label, saved, Lift.slots embed contents⟩ : TM2.Cfg (fun _ : Fin 3 => Bool) Λ σ) = _
      rw [beforeData]
    obtain ⟨posts, after, length, actual, finalLast, projection, frame⟩ :=
      Lift.path embed source rawBefore localBefore localAfter rest initial chain last
    have exactFinal : after = (⟨localAfter.l, localAfter.var, finalContents⟩ : TM2.Cfg Alphabet Λ σ) := by
      have position := congrArg (fun state => state.l) projection
      have saved := congrArg (fun state => state.var) projection
      have selected := congrArg (fun state => state.stk) projection
      change Lift.slots embed after.stk = localAfter.stk at selected
      have data := RatMarshal.selected_ext embed contents after.stk finalContents
        (selected.trans afterData.symm) frame outside
      rcases after with ⟨label, store, current⟩
      change label = localAfter.l at position
      change store = localAfter.var at saved
      change current = finalContents at data
      subst label
      subst store
      subst current
      rfl
    rw [exactFinal] at finalLast
    refine ⟨⟨rawBefore :: posts, rfl, actual, finalLast⟩, ?_⟩
    simp only [List.length_cons, length]

end PDROC.BitVM.Codec.FieldOps
