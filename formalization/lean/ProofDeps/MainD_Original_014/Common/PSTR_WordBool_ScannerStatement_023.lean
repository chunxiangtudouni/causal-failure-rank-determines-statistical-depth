module

public import Common.PSTR_WordBool_ScannerAction_022

/-! Actual whole-statement scanner paths, sharing each bottom-return transition
with the next statement entry. The clock counts real transitions after the
initial trNormal stepAux, without adding a fresh normal entry per stack action. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.ScannerStatement

open Turing ScannerPaths ScannerAction

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

def clock : TM2.Stmt Γ Λ σ → σ → (∀ k, List (Γ k)) → Nat
  | .push k value next, store, slots =>
      (slots k).length + (value store :: slots k).length + 2 +
        clock next store (Function.update slots k (value store :: slots k))
  | .peek k value next, store, slots =>
      (slots k).length + (slots k).length + 2 + clock next (value store (slots k).head?) slots
  | .pop k value next, store, slots =>
      (slots k).length + (slots k).tail.length + 2 +
        clock next (value store (slots k).head?) (Function.update slots k (slots k).tail)
  | .load value next, store, slots => clock next (value store) slots
  | .branch test yes no, store, slots => if test store then clock yes store slots else clock no store slots
  | .goto _, _, _ | .halt, _, _ => 0

theorem clock_run (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) :
    clock (TM2to1.stRun action next) store slots =
      (slots k).length + (TM2to1.stWrite store (slots k) action).length + 2 +
        clock next (TM2to1.stVar store (slots k) action)
          (Function.update slots k (TM2to1.stWrite store (slots k) action)) := by
  cases action with
  | push value => rfl
  | peek value => simp only [TM2to1.stRun, TM2to1.stWrite, TM2to1.stVar, clock, Function.update_eq_self]
  | pop value => rfl

theorem ret_bottom (machine : Λ → TM2.Stmt Γ Λ σ) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) :
    TM1.step (TM2to1.tr machine) (retCfg next store tracks 0) =
      some (TM1.stepAux (TM2to1.trNormal next) store (baseTape tracks)) := by
  simp only [retCfg, Function.iterate_zero_apply, TM1.step, TM2to1.tr, TM1.stepAux,
    baseTape, Tape.mk'_head, TM2to1.addBottom_head_fst, Bool.cond_true]

def representedFinal (statement : TM2.Stmt Γ Λ σ) (store : σ)
    (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k))) :
    ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) :=
  let final := TM2.stepAux statement store slots
  ⟨final.l.map TM2to1.Λ'.normal, final.var, baseTape tracks⟩

theorem statement_path (machine : Λ → TM2.Stmt Γ Λ σ) (statement : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((slots k).map some).reverse) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (trace : List (ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk (((TM2.stepAux statement store slots).stk k).map some).reverse) ∧
      trace.head? = some (TM1.stepAux (TM2to1.trNormal statement) store (baseTape tracks)) ∧
      trace.IsChain (fun before after => TM1.step (TM2to1.tr machine) before = some after) ∧
      trace.getLast? = some (representedFinal statement store slots changed) ∧
      trace.length = clock statement store slots + 1 := by
  induction statement using TM2to1.stmtStRec generalizing store slots tracks with
  | run k action next ih =>
    let updated := Function.update slots k (TM2to1.stWrite store (slots k) action)
    let updatedStore := TM2to1.stVar store (slots k) action
    obtain ⟨middle, scanning, middleRep, scanFirst, scanChain, scanLast, scanLength⟩ :=
      action_path machine k action next store slots tracks represented
    obtain ⟨changed, later, changedRep, laterFirst, laterChain, laterLast, laterLength⟩ :=
      ih updatedStore updated middle middleRep
    have chain : (scanning ++ later).IsChain
        (fun before after => TM1.step (TM2to1.tr machine) before = some after) := by
      apply scanChain.append laterChain
      intro before beforeLast after afterFirst
      rw [scanLast] at beforeLast
      rw [laterFirst] at afterFirst
      have sameBefore := Option.some.inj (Option.mem_def.mp beforeLast)
      have sameAfter := Option.some.inj (Option.mem_def.mp afterFirst)
      subst before
      subst after
      exact ret_bottom machine next updatedStore middle
    refine ⟨changed, scanning ++ later, ?_, ?_, chain, ?_, ?_⟩
    · simpa only [TM2to1.step_run] using changedRep
    · rw [List.head?_append, scanFirst]
      rw [TM2to1.trNormal_run]
      rfl
    · rw [List.getLast?_append, laterLast]
      change some (representedFinal next updatedStore updated changed) = _
      simp only [representedFinal, TM2to1.step_run, updatedStore, updated]
    · rw [List.length_append, scanLength, laterLength, clock_run]
      rfl
  | load value next ih =>
    simpa only [TM2.stepAux, TM2to1.trNormal, TM1.stepAux, clock, representedFinal]
      using ih (value store) slots tracks represented
  | branch test yes no ihYes ihNo =>
    cases choice : test store
    · simpa only [TM2.stepAux, TM2to1.trNormal, TM1.stepAux, clock, representedFinal,
        choice, Bool.cond_false, Bool.false_eq_true, ite_false]
        using ihNo store slots tracks represented
    · simpa only [TM2.stepAux, TM2to1.trNormal, TM1.stepAux, clock, representedFinal,
        choice, Bool.cond_true, ite_true]
        using ihYes store slots tracks represented
  | goto label =>
    refine ⟨tracks, [representedFinal (.goto label) store slots tracks], represented, rfl,
      List.isChain_singleton _, rfl, rfl⟩
  | halt =>
    refine ⟨tracks, [representedFinal .halt store slots tracks], represented, rfl,
      List.isChain_singleton _, rfl, rfl⟩

end PaperProofs.Common.Native.PSTRWordBool.ScannerStatement
