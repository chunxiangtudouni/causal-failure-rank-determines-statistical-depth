module

public import Common.PSTR_WordBool_ScannerPaths_021

/-! One actual stack action with the SAME updated track witness as Mathlib's
exact stepAux theorem, surrounded by explicit go/return lists. No head reset,
new representation oracle, or qualitative reachability clock is introduced.
Internal moves within the action still require their own physical range proof. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.ScannerAction

open Turing ScannerPaths

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

omit [DecidableEq K] in
theorem go_head (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (goTrace k action next store tracks distance).head? = some (goCfg k action next store tracks 0) := by
  simp only [goTrace, List.head?_map, List.head?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Option.map_some]

omit [DecidableEq K] in
theorem go_last (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (goTrace k action next store tracks distance).getLast? = some (goCfg k action next store tracks distance) := by
  simp only [goTrace, List.getLast?_map, List.getLast?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, Option.map_some]

omit [DecidableEq K] in
theorem ret_head (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (retTrace next store tracks distance).head? = some (retCfg next store tracks distance) := by
  simp only [retTrace, List.head?_map, List.head?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Option.map_some, Nat.sub_zero]

omit [DecidableEq K] in
theorem ret_last (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (retTrace next store tracks distance).getLast? = some (retCfg next store tracks 0) := by
  simp only [retTrace, List.getLast?_map, List.getLast?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, Option.map_some, Nat.sub_self]

variable (machine : Λ → TM2.Stmt Γ Λ σ)

theorem actual_action (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((slots k).map some).reverse) :
    ∃ changed : ListBlank (∀ k, Option (Γ k)),
      (∀ other, changed.map (proj other) = ListBlank.mk
        (((Function.update slots k (TM2to1.stWrite store (slots k) action)) other).map some).reverse) ∧
      TM1.step (TM2to1.tr machine) (goCfg k action next store tracks (slots k).length) =
        some (retCfg next (TM2to1.stVar store (slots k) action) changed
          (TM2to1.stWrite store (slots k) action).length) := by
  obtain ⟨changed, changedRep, step⟩ := TM2to1.tr_respects_aux₂
    (q := TM1.Stmt.goto (fun _ _ => TM2to1.Λ'.ret next)) represented action
  refine ⟨changed, changedRep, ?_⟩
  unfold goCfg retCfg baseTape
  simp only [TM1.step, TM2to1.tr, TM1.stepAux, Tape.move_right_n_head,
    Tape.mk'_nth_nat, TM2to1.addBottom_nth_snd]
  rw [TM2to1.stk_nth_val _ (represented k),
    List.getElem?_eq_none (le_of_eq List.length_reverse)]
  change some (TM1.stepAux (TM2to1.trStAct
    (TM1.Stmt.goto (fun _ _ => TM2to1.Λ'.ret next)) action) store
      ((Tape.move .right)^[(slots k).length] (Tape.mk' ∅ (TM2to1.addBottom tracks)))) = _
  simp only [Function.update_self, TM1.stepAux] at step
  exact congrArg some step

theorem action_path (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((slots k).map some).reverse) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (trace : List (ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ other, changed.map (proj other) = ListBlank.mk
        (((Function.update slots k (TM2to1.stWrite store (slots k) action)) other).map some).reverse) ∧
      trace.head? = some (goCfg k action next store tracks 0) ∧
      trace.IsChain (fun before after => TM1.step (TM2to1.tr machine) before = some after) ∧
      trace.getLast? = some (retCfg next (TM2to1.stVar store (slots k) action) changed 0) ∧
      trace.length = (slots k).length + (TM2to1.stWrite store (slots k) action).length + 2 := by
  obtain ⟨changed, changedRep, edge⟩ := actual_action machine k action next store slots tracks represented
  let outward := goTrace k action next store tracks (slots k).length
  let returning := retTrace next (TM2to1.stVar store (slots k) action) changed
    (TM2to1.stWrite store (slots k) action).length
  have outwardFirst := go_head k action next store tracks (slots k).length
  have outwardLast := go_last k action next store tracks (slots k).length
  have returningFirst := ret_head next (TM2to1.stVar store (slots k) action) changed
    (TM2to1.stWrite store (slots k) action).length
  have returningLast := ret_last next (TM2to1.stVar store (slots k) action) changed
    (TM2to1.stWrite store (slots k) action).length
  have chain : (outward ++ returning).IsChain
      (fun before after => TM1.step (TM2to1.tr machine) before = some after) := by
    apply (go_chain machine k action next store (slots k) tracks (represented k) _ le_rfl).append
      (ret_chain machine next (TM2to1.stVar store (slots k) action) changed _)
    intro before beforeLast after afterFirst
    rw [outwardLast] at beforeLast
    rw [returningFirst] at afterFirst
    have sameBefore := Option.some.inj (Option.mem_def.mp beforeLast)
    have sameAfter := Option.some.inj (Option.mem_def.mp afterFirst)
    subst before
    subst after
    exact edge
  refine ⟨changed, outward ++ returning, changedRep, ?_, chain, ?_, ?_⟩
  · rw [List.head?_append, outwardFirst]
    rfl
  · rw [List.getLast?_append, returningLast]
    rfl
  · dsimp only [outward, returning]
    rw [List.length_append, go_length, ret_length]
    omega

end PaperProofs.Common.Native.PSTRWordBool.ScannerAction
