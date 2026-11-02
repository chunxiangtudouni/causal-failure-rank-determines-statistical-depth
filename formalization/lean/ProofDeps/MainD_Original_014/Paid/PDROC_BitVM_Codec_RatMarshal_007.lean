module

public import Paid.PDROC_BitVM_Codec_RatMarshal_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.BitVM.Codec.RatMarshal

open Turing PDROC.BitVM.Native

structure Trace (machine : Label → Statement) (before after : State) where
  states : List State
  first : states.head? = some before
  actual : states.IsChain (fun a b => TM2.step machine a = some b)
  last : states.getLast? = some after

theorem joined_last (left right : List State) (middle after : State)
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

def Trace.append {machine : Label → Statement} {before middle after : State}
    (left : Trace machine before middle) (right : Trace machine middle after) : Trace machine before after where
  states := left.states ++ right.states.tail
  first := by simp only [List.head?_append, left.first, Option.some_or]
  actual := PDROC.BitVM.Log.TwoStack.join_chain left.states right.states middle
    left.actual right.actual left.last right.first
  last := joined_last left.states right.states middle after left.last right.first right.last

theorem Trace.append_length {machine : Label → Statement} {before middle after : State}
    (left : Trace machine before middle) (right : Trace machine middle after) :
    (left.append right).states.length ≤ left.states.length + right.states.length := by
  simp only [Trace.append, List.length_append, List.length_tail]
  omega

def Trace.single {machine : Label → Statement} {before after : State}
    (edge : TM2.step machine before = some after) : Trace machine before after :=
  ⟨[before, after], rfl, List.isChain_cons_cons.mpr ⟨edge, List.isChain_singleton _⟩, rfl⟩

theorem selected_ext (embed : Fin 3 ↪ Stack) (old actual expected : Stack → List Bool)
    (selected : Lift.slots embed actual = Lift.slots embed expected)
    (actualFrame : ∀ other, (∀ role, other ≠ embed role) → actual other = old other)
    (expectedFrame : ∀ other, (∀ role, other ≠ embed role) → expected other = old other) :
    actual = expected := by
  funext other
  by_cases at0 : other = embed 0
  · subst other
    exact congrFun selected 0
  by_cases at1 : other = embed 1
  · subst other
    exact congrFun selected 1
  by_cases at2 : other = embed 2
  · subst other
    exact congrFun selected 2
  have outside : ∀ role, other ≠ embed role := by
    intro role
    fin_cases role
    · exact at0
    · exact at1
    · exact at2
  exact (actualFrame other outside).trans (expectedFrame other outside).symm

/-- Thin composition of the existing genuine Lift and Inline trace laws.
The selected-data equations describe explicit before/after bytes of an
already-proved local run; callers below construct them from actual reads.
They are not additional premises of the exported Rat reader theorem. -/
theorem call_three {Λ : Type*} (embed : Fin 3 ↪ Stack)
    (source : Λ → TM2.Stmt (fun _ : Fin 3 => Bool) Λ (Option Bool))
    (caller : Label → Statement) (labels : Λ → Label) (returnLabel : Label)
    (agrees : ∀ label, caller (labels label) =
      Inline.statement labels returnLabel (Lift.machine embed source label))
    (originalBefore originalAfter : TM2.Cfg (fun _ : Fin 3 => Bool) Λ (Option Bool))
    (localRun : List (TM2.Cfg (fun _ : Fin 3 => Bool) Λ (Option Bool)))
    (head : localRun.head? = some originalBefore)
    (chain : localRun.IsChain (fun a b => TM2.step source a = some b))
    (last : localRun.getLast? = some originalAfter) (halted : originalAfter.l = none)
    (contents finalContents : Stack → List Bool) (sign : Bool)
    (beforeData : Lift.slots embed contents = originalBefore.stk)
    (afterData : Lift.slots embed finalContents = originalAfter.stk)
    (outside : ∀ other, (∀ role, other ≠ embed role) → finalContents other = contents other) :
    ∃ path : Trace caller
      (Inline.cfg labels returnLabel sign
        (⟨originalBefore.l, originalBefore.var, contents⟩ : TM2.Cfg Alphabet Λ (Option Bool)))
      (⟨some returnLabel, (originalAfter.var, sign), finalContents⟩ : State),
      path.states.length = localRun.length := by
  cases localRun with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons first rest =>
    have same : first = originalBefore := Option.some.inj head
    subst first
    let rawBefore : TM2.Cfg Alphabet Λ (Option Bool) :=
      ⟨originalBefore.l, originalBefore.var, contents⟩
    have initial : Lift.cfg embed rawBefore = originalBefore := by
      rcases originalBefore with ⟨label, saved, selectedData⟩
      change Lift.slots embed contents = selectedData at beforeData
      change (⟨label, saved, Lift.slots embed contents⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) Λ (Option Bool)) = _
      rw [beforeData]
    obtain ⟨posts, final, length, actual, finalLast, projection, frame⟩ :=
      Lift.path embed source rawBefore originalBefore originalAfter rest initial chain last
    have exactFinal : final = (⟨none, originalAfter.var, finalContents⟩ :
        TM2.Cfg Alphabet Λ (Option Bool)) := by
      have position := (congrArg (fun state => state.l) projection).trans halted
      have saved := congrArg (fun state => state.var) projection
      have data := congrArg (fun state => state.stk) projection
      change Lift.slots embed final.stk = originalAfter.stk at data
      have selectedData := selected_ext embed contents final.stk finalContents
        (data.trans afterData.symm) frame outside
      rcases final with ⟨label, store, contents⟩
      change label = none at position
      change store = originalAfter.var at saved
      change contents = finalContents at selectedData
      subst label
      subst store
      subst contents
      rfl
    rw [exactFinal] at finalLast
    let transform : TM2.Cfg Alphabet Λ (Option Bool) → State := Inline.cfg labels returnLabel sign
    let mapped := (rawBefore :: posts).map transform
    have mappedHead : mapped.head? = some (transform rawBefore) := rfl
    have mappedChain : mapped.IsChain (fun a b => TM2.step caller a = some b) := by
      exact List.isChain_map_of_isChain _
        (fun a b edge => Inline.step_edge labels returnLabel (Lift.machine embed source)
          caller agrees a b sign edge) actual
    have mappedLast : mapped.getLast? = some (⟨some returnLabel,
        (originalAfter.var, sign), finalContents⟩ : State) := by
      simp only [mapped, List.getLast?_map, finalLast, Option.map_some, transform, Inline.cfg,
        Option.map_none, Option.getD_none]
    refine ⟨⟨mapped, mappedHead, mappedChain, mappedLast⟩, ?_⟩
    simp only [mapped, List.length_map, List.length_cons, length]

theorem reset_step (source : Register) (num den : Fin 7) (different : num ≠ den)
    (contents : Stack → List Bool) (store : Store) :
    TM2.step (program source num den different) (⟨some 0, store, contents⟩ : State) =
      some (⟨some 1, (none, false), contents⟩ : State) := rfl

theorem tag_step (source : Register) (num den : Fin 7) (different : num ≠ den)
    (contents : Stack → List Bool) (fields : List Bool) (sign : Bool) (oldStore : Store)
    (input : contents 0 = true :: sign :: fields) :
    TM2.step (program source num den different) (⟨some 6, oldStore, contents⟩ : State) =
      some (⟨some 7, (none, sign), Function.update contents 0 fields⟩ : State) := by
  have updated : Function.update (Function.update contents 0 (sign :: fields)) 0 fields =
      Function.update contents 0 fields := by
    funext role
    by_cases at0 : role = 0 <;> simp_all
  change some (TM2.stepAux tagCode oldStore contents) = _
  simp only [tagCode, TM2.stepAux, input, List.head?_cons, List.tail_cons,
    Function.update_self, beq_self_eq_true, Bool.cond_true, Option.isSome_some,
    Option.getD_some]
  rw [updated]

theorem halt_step (source : Register) (num den : Fin 7) (different : num ≠ den)
    (contents : Stack → List Bool) (store : Store) :
    TM2.step (program source num den different) (⟨some 17, store, contents⟩ : State) =
      some (⟨none, store, contents⟩ : State) := rfl

end PDROC.BitVM.Codec.RatMarshal
