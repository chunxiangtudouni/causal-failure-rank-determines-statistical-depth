module

public import Common.PSTR_WordBool_LocatedScanner_029
public import Common.PSTR_WordBool_ScannerClock_024

/-! Coupled count and physical Gamma coordinates for ONE actual whole-statement
trace. The global node bound is derived from entrance occupancy and source
syntax; it is not an additional original caller resource certificate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.LocatedStatement

open Turing ScannerPaths ScannerStatement ScannerDisplacement

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

theorem node_head (statement : TM2.Stmt Γ Λ σ) (store : σ) (slots : ∀ k, List (Γ k)) :
    (store, slots) ∈ AuxWorkspace.nodes statement store slots := by
  cases statement <;> exact List.mem_cons_self

theorem nodes_run (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) :
    AuxWorkspace.nodes (TM2to1.stRun action next) store slots = (store, slots) ::
      AuxWorkspace.nodes next (TM2to1.stVar store (slots k) action)
        (Function.update slots k (TM2to1.stWrite store (slots k) action)) := by
  cases action with
  | push value => rfl
  | peek value =>
    simp only [TM2to1.stRun, TM2to1.stWrite, TM2to1.stVar, AuxWorkspace.nodes, Function.update_eq_self]
  | pop value => rfl

theorem path_of_nodes (machine : Λ → TM2.Stmt Γ Λ σ) (statement : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((slots k).map some).reverse)
    (span : Nat) (bounded : ∀ snapshot ∈ AuxWorkspace.nodes statement store slots,
      ∀ k, (snapshot.2 k).length ≤ span) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (trace : List (LocatedScanner.Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk (((TM2.stepAux statement store slots).stk k).map some).reverse) ∧
      trace.head? = some (TM1.stepAux (TM2to1.trNormal statement) store (baseTape tracks), 0) ∧
      trace.IsChain (LocatedScanner.Step machine) ∧
      trace.getLast? = some (representedFinal statement store slots changed, 0) ∧
      trace.length = clock statement store slots + 1 ∧
      ∀ point ∈ trace, 0 ≤ point.2 ∧ point.2 ≤ (span : Int) := by
  induction statement using TM2to1.stmtStRec generalizing store slots tracks with
  | run k action next ih =>
    let nextSlots := Function.update slots k (TM2to1.stWrite store (slots k) action)
    let nextStore := TM2to1.stVar store (slots k) action
    have tailBounded : ∀ snapshot ∈ AuxWorkspace.nodes next nextStore nextSlots,
        ∀ other, (snapshot.2 other).length ≤ span := by
      intro snapshot present other
      apply bounded snapshot ?_ other
      rw [nodes_run]
      exact List.mem_cons_of_mem _ present
    have entryWidth : (slots k).length ≤ span :=
      bounded (store, slots) (node_head (TM2to1.stRun action next) store slots) k
    have exitWidth : (TM2to1.stWrite store (slots k) action).length ≤ span := by
      have result := tailBounded (nextStore, nextSlots) (node_head next nextStore nextSlots) k
      simpa only [nextSlots, Function.update_self] using result
    have maxWidth := Nat.max_le.mpr ⟨entryWidth, exitWidth⟩
    obtain ⟨middle, scanning, middleRep, scanFirst, scanChain, scanLast, scanLength, scanRange⟩ :=
      LocatedScanner.action_path machine k action next store slots tracks represented
    obtain ⟨changed, later, changedRep, laterFirst, laterChain, laterLast, laterLength, laterRange⟩ :=
      ih nextStore nextSlots middle middleRep tailBounded
    have chain : (scanning ++ later).IsChain (LocatedScanner.Step machine) := by
      apply scanChain.append laterChain
      intro before beforeLast after afterFirst
      rw [scanLast] at beforeLast
      rw [laterFirst] at afterFirst
      have sameBefore := Option.some.inj (Option.mem_def.mp beforeLast)
      have sameAfter := Option.some.inj (Option.mem_def.mp afterFirst)
      subst before
      subst after
      refine ⟨ret_bottom machine next nextStore middle, ?_⟩
      change (0 : Int) = 0 + StatementDisplacement.netMove
        (TM2to1.tr machine (.ret next)) nextStore (baseTape middle)
      simp only [ret_bottom_net, Int.add_zero]
    refine ⟨changed, scanning ++ later, ?_, ?_, chain, ?_, ?_, ?_⟩
    · simpa only [TM2to1.step_run] using changedRep
    · rw [List.head?_append, scanFirst, TM2to1.trNormal_run]
      rfl
    · rw [List.getLast?_append, laterLast]
      simp only [Option.some_or, representedFinal, TM2to1.step_run, nextStore, nextSlots]
    · rw [List.length_append, scanLength, laterLength, clock_run]
      rfl
    · intro point present
      rcases List.mem_append.mp present with first | last
      · have within := scanRange point first
        constructor <;> omega
      · exact laterRange point last
  | load value next ih =>
    have tailBounded : ∀ snapshot ∈ AuxWorkspace.nodes next (value store) slots,
        ∀ k, (snapshot.2 k).length ≤ span := by
      intro snapshot present k
      exact bounded snapshot (List.mem_cons_of_mem _ present) k
    simpa only [TM2.stepAux, TM2to1.trNormal, TM1.stepAux, clock, representedFinal]
      using ih (value store) slots tracks represented tailBounded
  | branch test yes no ihYes ihNo =>
    cases choice : test store
    · have tailBounded : ∀ snapshot ∈ AuxWorkspace.nodes no store slots,
          ∀ k, (snapshot.2 k).length ≤ span := by
        intro snapshot present k
        apply bounded snapshot ?_ k
        simpa only [AuxWorkspace.nodes, choice, Bool.false_eq_true, ite_false]
          using List.mem_cons_of_mem (store, slots) present
      simpa only [TM2.stepAux, TM2to1.trNormal, TM1.stepAux, clock, representedFinal,
        choice, Bool.cond_false, Bool.false_eq_true, ite_false]
        using ihNo store slots tracks represented tailBounded
    · have tailBounded : ∀ snapshot ∈ AuxWorkspace.nodes yes store slots,
          ∀ k, (snapshot.2 k).length ≤ span := by
        intro snapshot present k
        apply bounded snapshot ?_ k
        simpa only [AuxWorkspace.nodes, choice, ite_true]
          using List.mem_cons_of_mem (store, slots) present
      simpa only [TM2.stepAux, TM2to1.trNormal, TM1.stepAux, clock, representedFinal,
        choice, Bool.cond_true, ite_true]
        using ihYes store slots tracks represented tailBounded
  | goto label =>
    refine ⟨tracks, [(representedFinal (.goto label) store slots tracks, 0)], represented, rfl,
      List.isChain_singleton _, rfl, rfl, ?_⟩
    intro point present
    have same := List.mem_singleton.mp present
    subst point
    constructor <;> omega
  | halt =>
    refine ⟨tracks, [(representedFinal .halt store slots tracks, 0)], represented, rfl,
      List.isChain_singleton _, rfl, rfl, ?_⟩
    intro point present
    have same := List.mem_singleton.mp present
    subst point
    constructor <;> omega

theorem actual_path (machine : Λ → TM2.Stmt Γ Λ σ) (statement : TM2.Stmt Γ Λ σ)
    (store : σ) (slots : ∀ k, List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((slots k).map some).reverse)
    (bound : Nat) (bounded : ∀ k, (slots k).length ≤ bound) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (trace : List (LocatedScanner.Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk (((TM2.stepAux statement store slots).stk k).map some).reverse) ∧
      trace.head? = some (TM1.stepAux (TM2to1.trNormal statement) store (baseTape tracks), 0) ∧
      trace.IsChain (LocatedScanner.Step machine) ∧
      trace.getLast? = some (representedFinal statement store slots changed, 0) ∧
      trace.length = clock statement store slots + 1 ∧
      trace.length ≤ 2 * ScannerClock.actions statement * (bound + AuxWorkspace.pushes statement + 1) + 1 ∧
      ∀ point ∈ trace, 0 ≤ point.2 ∧ point.2 ≤ ((bound + AuxWorkspace.pushes statement : Nat) : Int) := by
  have allBounded := AuxWorkspace.node_bound statement store slots bound bounded
  obtain ⟨changed, trace, changedRep, first, chain, last, length, coordinates⟩ :=
    path_of_nodes machine statement store slots tracks represented
      (bound + AuxWorkspace.pushes statement) allBounded
  refine ⟨changed, trace, changedRep, first, chain, last, length, ?_, coordinates⟩
  rw [length]
  exact Nat.add_le_add_right (ScannerClock.clock_bound statement store slots bound bounded) 1

end PaperProofs.Common.Native.PSTRWordBool.LocatedStatement
