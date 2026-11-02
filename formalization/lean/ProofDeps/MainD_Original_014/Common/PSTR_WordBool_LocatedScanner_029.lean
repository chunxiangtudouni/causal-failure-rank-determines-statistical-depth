module

public import Common.PSTR_WordBool_ScannerAction_022
public import Common.PSTR_WordBool_ScannerDisplacement_028

/-! Actual scanner paths annotated with proof-only physical head coordinates.
The go/act/return endpoints lie between zero and the larger actual stack size.
Every edge checks both the real TM1 transition and its exact physical net move.
No coordinate is stored in the runtime machine. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.LocatedScanner

open Turing ScannerPaths ScannerAction ScannerDisplacement

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

abbrev Located := ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) × Int

def net (machine : Λ → TM2.Stmt Γ Λ σ)
    (state : ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) : Int :=
  match state.l with
  | none => 0
  | some label => StatementDisplacement.netMove (TM2to1.tr machine label) state.var state.Tape

def Step (machine : Λ → TM2.Stmt Γ Λ σ)
    (before after : Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) : Prop :=
  TM1.step (TM2to1.tr machine) before.1 = some after.1 ∧ after.2 = before.2 + net machine before.1

def goLocated (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    List (Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) :=
  (List.range (distance + 1)).map (fun index => (goCfg k action next store tracks index, (index : Int)))

def retLocated (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    List (Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) :=
  (List.range (distance + 1)).map (fun index =>
    (retCfg next store tracks (distance - index), ((distance - index : Nat) : Int)))

omit [DecidableEq K] in
theorem go_head (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (goLocated k action next store tracks distance).head? = some (goCfg k action next store tracks 0, 0) := by
  simp only [goLocated, List.head?_map, List.head?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Option.map_some, Int.natCast_zero]

omit [DecidableEq K] in
theorem go_last (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (goLocated k action next store tracks distance).getLast? =
      some (goCfg k action next store tracks distance, (distance : Int)) := by
  simp only [goLocated, List.getLast?_map, List.getLast?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, Option.map_some]

omit [DecidableEq K] in
theorem ret_head (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (retLocated next store tracks distance).head? = some (retCfg next store tracks distance, (distance : Int)) := by
  simp only [retLocated, List.head?_map, List.head?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Option.map_some, Nat.sub_zero]

omit [DecidableEq K] in
theorem ret_last (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (retLocated next store tracks distance).getLast? = some (retCfg next store tracks 0, 0) := by
  simp only [retLocated, List.getLast?_map, List.getLast?_range, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel, Option.map_some, Nat.sub_self,
    Int.natCast_zero]

omit [DecidableEq K] in
theorem go_range (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    ∀ point ∈ goLocated k action next store tracks distance,
      0 ≤ point.2 ∧ point.2 ≤ (distance : Int) := by
  intro point present
  obtain ⟨index, within, equal⟩ := List.mem_map.mp present
  subst point
  have less := List.mem_range.mp within
  dsimp only
  constructor <;> omega

omit [DecidableEq K] in
theorem ret_range (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    ∀ point ∈ retLocated next store tracks distance,
      0 ≤ point.2 ∧ point.2 ≤ (distance : Int) := by
  intro point present
  obtain ⟨index, _, equal⟩ := List.mem_map.mp present
  subst point
  have less := Nat.sub_le distance index
  dsimp only
  constructor <;> omega

variable (machine : Λ → TM2.Stmt Γ Λ σ)

theorem go_chain (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (stack : List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : tracks.map (proj k) = ListBlank.mk (stack.map some).reverse)
    (distance : Nat) (within : distance ≤ stack.length) :
    (goLocated k action next store tracks distance).IsChain (Step machine) := by
  apply (List.isChain_map _).2
  apply (List.isChain_range_succ _ distance).2
  intro index before
  refine ⟨ScannerPaths.go_step machine k action next store stack tracks represented index
    (before.trans_le within), ?_⟩
  change ((index + 1 : Nat) : Int) = (index : Int) +
    StatementDisplacement.netMove (TM2to1.tr machine (.go k action next)) store
      ((Tape.move .right)^[index] (baseTape tracks))
  rw [go_scan_net machine k action next store stack tracks represented index (before.trans_le within)]
  omega

theorem ret_chain (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (retLocated next store tracks distance).IsChain (Step machine) := by
  apply (List.isChain_map _).2
  apply (List.isChain_range_succ _ distance).2
  intro index before
  have subtract : distance - index = (distance - (index + 1)) + 1 := by omega
  constructor
  · change TM1.step (TM2to1.tr machine) (retCfg next store tracks (distance - index)) = _
    rw [subtract]
    exact ScannerPaths.ret_step machine next store tracks (distance - (index + 1))
  · change ((distance - (index + 1) : Nat) : Int) = ((distance - index : Nat) : Int) +
      StatementDisplacement.netMove (TM2to1.tr machine (.ret next)) store
        ((Tape.move .right)^[distance - index] (baseTape tracks))
    rw [subtract, ret_scan_net]
    omega

theorem action_path (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((slots k).map some).reverse) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (trace : List (Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ other, changed.map (proj other) = ListBlank.mk
        (((Function.update slots k (TM2to1.stWrite store (slots k) action)) other).map some).reverse) ∧
      trace.head? = some (goCfg k action next store tracks 0, 0) ∧
      trace.IsChain (Step machine) ∧
      trace.getLast? = some (retCfg next (TM2to1.stVar store (slots k) action) changed 0, 0) ∧
      trace.length = (slots k).length + (TM2to1.stWrite store (slots k) action).length + 2 ∧
      ∀ point ∈ trace, 0 ≤ point.2 ∧ point.2 ≤
        (max (slots k).length (TM2to1.stWrite store (slots k) action).length : Int) := by
  obtain ⟨changed, changedRep, edge⟩ := ScannerAction.actual_action machine k action next store slots tracks represented
  let outward := goLocated k action next store tracks (slots k).length
  let returning := retLocated next (TM2to1.stVar store (slots k) action) changed
    (TM2to1.stWrite store (slots k) action).length
  have outwardFirst := go_head k action next store tracks (slots k).length
  have outwardLast := go_last k action next store tracks (slots k).length
  have returningFirst := ret_head next (TM2to1.stVar store (slots k) action) changed
    (TM2to1.stWrite store (slots k) action).length
  have returningLast := ret_last next (TM2to1.stVar store (slots k) action) changed
    (TM2to1.stWrite store (slots k) action).length
  have chain : (outward ++ returning).IsChain (Step machine) := by
    apply (go_chain machine k action next store (slots k) tracks (represented k) _ le_rfl).append
      (ret_chain machine next (TM2to1.stVar store (slots k) action) changed _)
    intro before beforeLast after afterFirst
    rw [outwardLast] at beforeLast
    rw [returningFirst] at afterFirst
    have sameBefore := Option.some.inj (Option.mem_def.mp beforeLast)
    have sameAfter := Option.some.inj (Option.mem_def.mp afterFirst)
    subst before
    subst after
    refine ⟨edge, ?_⟩
    change ((TM2to1.stWrite store (slots k) action).length : Int) = ((slots k).length : Int) +
      StatementDisplacement.netMove (TM2to1.tr machine (.go k action next)) store
        ((Tape.move .right)^[(slots k).length] (baseTape tracks))
    rw [go_action_net machine k action next store (slots k) tracks (represented k)]
    omega
  refine ⟨changed, outward ++ returning, changedRep, ?_, chain, ?_, ?_, ?_⟩
  · rw [List.head?_append, outwardFirst]
    rfl
  · rw [List.getLast?_append, returningLast]
    rfl
  · dsimp only [outward, returning]
    simp only [List.length_append, goLocated, retLocated, List.length_map, List.length_range]
    omega
  · intro point present
    rcases List.mem_append.mp present with first | last
    · have within := go_range k action next store tracks (slots k).length point first
      have upper := Nat.le_max_left (slots k).length (TM2to1.stWrite store (slots k) action).length
      constructor <;> omega
    · have within := ret_range next (TM2to1.stVar store (slots k) action) changed
        (TM2to1.stWrite store (slots k) action).length point last
      have upper := Nat.le_max_right (slots k).length (TM2to1.stWrite store (slots k) action).length
      constructor <;> omega

end PaperProofs.Common.Native.PSTRWordBool.LocatedScanner
