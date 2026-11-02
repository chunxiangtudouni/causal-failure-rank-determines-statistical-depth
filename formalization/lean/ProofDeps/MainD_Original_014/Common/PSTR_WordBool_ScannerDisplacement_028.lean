module

public import Common.PSTR_WordBool_ScannerPaths_021
public import Common.PSTR_WordBool_StatementDisplacement_026

/-! Exact physical net movements of the ACTUAL TM2-to-TM1 scanner statements.
These equations align explicit go/return list indices with head coordinates.
The native static-radius theorem separately covers all internal moves. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.ScannerDisplacement

open Turing ScannerPaths StatementDisplacement

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

omit [DecidableEq K] in
theorem normal_zero (statement : TM2.Stmt Γ Λ σ) (store : σ) (tape : Tape (TM2to1.Γ' K Γ)) :
    netMove (TM2to1.trNormal statement) store tape = 0 := by
  induction statement generalizing store tape with
  | push k value next ih => rfl
  | peek k value next ih => rfl
  | pop k value next ih => rfl
  | load value next ih => exact ih (value store) tape
  | branch test yes no ihYes ihNo =>
    dsimp only [TM2to1.trNormal, netMove]
    cases test store <;> first | exact ihYes store tape | exact ihNo store tape
  | goto label => rfl
  | halt => rfl

variable (machine : Λ → TM2.Stmt Γ Λ σ)

theorem go_scan_net (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (stack : List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : tracks.map (proj k) = ListBlank.mk (stack.map some).reverse)
    (index : Nat) (before : index < stack.length) :
    netMove (TM2to1.tr machine (.go k action next)) store
      ((Tape.move .right)^[index] (baseTape tracks)) = 1 := by
  simp only [TM2to1.tr, netMove, baseTape, Tape.move_right_n_head, Tape.mk'_nth_nat,
    TM2to1.addBottom_nth_snd]
  rw [TM2to1.stk_nth_val _ represented,
    List.getElem?_eq_getElem (by simpa only [List.length_reverse] using before)]
  rfl

theorem ret_scan_net (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (index : Nat) :
    netMove (TM2to1.tr machine (.ret next)) store
      ((Tape.move .right)^[index + 1] (baseTape tracks)) = -1 := by
  simp only [TM2to1.tr, netMove, baseTape, Tape.move_right_n_head, Tape.mk'_nth_nat,
    TM2to1.addBottom_nth_succ_fst, Bool.cond_false, delta, Int.add_zero]

theorem ret_bottom_net (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) :
    netMove (TM2to1.tr machine (.ret next)) store (baseTape tracks) = 0 := by
  simp only [TM2to1.tr, netMove, baseTape, Tape.mk'_head,
    TM2to1.addBottom_head_fst, Bool.cond_true]
  exact normal_zero next store (Tape.mk' ∅ (TM2to1.addBottom tracks))

theorem action_net (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (stack : List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k))) :
    netMove (TM2to1.trStAct (TM1.Stmt.goto (fun _ _ => TM2to1.Λ'.ret next)) action) store
      ((Tape.move .right)^[stack.length] (baseTape tracks)) =
      ((TM2to1.stWrite store stack action).length : Int) - (stack.length : Int) := by
  cases action with
  | push value =>
    simp only [TM2to1.trStAct, netMove, delta, TM2to1.stWrite, List.length_cons]
    omega
  | peek value =>
    simp only [TM2to1.trStAct, netMove, delta, TM2to1.stWrite]
    omega
  | pop value =>
    cases stack with
    | nil =>
      simp only [List.length_nil, Function.iterate_zero_apply, TM2to1.trStAct, netMove,
        baseTape, Tape.mk'_head, TM2to1.addBottom_head_fst, Bool.cond_true,
        TM2to1.stWrite, List.tail_nil]
      rfl
    | cons head tail =>
      simp only [List.length_cons, TM2to1.trStAct, netMove, baseTape,
        Tape.move_right_n_head, Tape.mk'_nth_nat, TM2to1.addBottom_nth_succ_fst,
        Bool.cond_false, delta, TM2to1.stWrite, List.tail_cons]
      omega

theorem go_action_net (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (stack : List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : tracks.map (proj k) = ListBlank.mk (stack.map some).reverse) :
    netMove (TM2to1.tr machine (.go k action next)) store
      ((Tape.move .right)^[stack.length] (baseTape tracks)) =
      ((TM2to1.stWrite store stack action).length : Int) - (stack.length : Int) := by
  change cond ((((Tape.move .right)^[stack.length] (baseTape tracks)).head.2 k).isNone)
    (netMove (TM2to1.trStAct (TM1.Stmt.goto (fun _ _ => TM2to1.Λ'.ret next)) action) store
      ((Tape.move .right)^[stack.length] (baseTape tracks))) _ = _
  have empty : (((Tape.move .right)^[stack.length] (baseTape tracks)).head.2 k) = none := by
    rw [baseTape, Tape.move_right_n_head, Tape.mk'_nth_nat, TM2to1.addBottom_nth_snd,
      TM2to1.stk_nth_val _ represented, List.getElem?_eq_none (le_of_eq List.length_reverse)]
  rw [empty]
  exact action_net k action next store stack tracks

end PaperProofs.Common.Native.PSTRWordBool.ScannerDisplacement
