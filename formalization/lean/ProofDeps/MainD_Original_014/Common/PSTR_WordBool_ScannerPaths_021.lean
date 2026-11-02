module

public import Common.PSTR_WordBool_AuxWorkspace_020
public import Mathlib.Data.List.Range

/-! Clocked actual go/return paths for the Mathlib TM2 scanner. These lists
contain every scanner TM1 configuration; qualitative Reaches0 is not used
to infer a clock. Internal action movements are a separate required proof. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.ScannerPaths

open Turing

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

abbrev State := TM1.Cfg (TM2to1.Γ' K Γ) (TM2to1.Λ' K Γ Λ σ) σ

def baseTape (tracks : ListBlank (∀ k, Option (Γ k))) : Tape (TM2to1.Γ' K Γ) :=
  Tape.mk' ∅ (TM2to1.addBottom tracks)

def goCfg (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (index : Nat) :
    State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) :=
  ⟨some (.go k action next), store, (Tape.move .right)^[index] (baseTape tracks)⟩

def retCfg (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (index : Nat) :
    State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) :=
  ⟨some (.ret next), store, (Tape.move .right)^[index] (baseTape tracks)⟩

variable (machine : Λ → TM2.Stmt Γ Λ σ)

theorem go_step (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (stack : List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : tracks.map (proj k) = ListBlank.mk (stack.map some).reverse)
    (index : Nat) (before : index < stack.length) :
    TM1.step (TM2to1.tr machine) (goCfg k action next store tracks index) =
      some (goCfg k action next store tracks (index + 1)) := by
  unfold goCfg baseTape
  rw [Function.iterate_succ_apply']
  simp only [TM1.step, TM1.stepAux, TM2to1.tr, Tape.mk'_nth_nat,
    Tape.move_right_n_head, TM2to1.addBottom_nth_snd]
  rw [TM2to1.stk_nth_val _ represented,
    List.getElem?_eq_getElem (by simpa only [List.length_reverse] using before)]
  rfl

theorem ret_step (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (index : Nat) :
    TM1.step (TM2to1.tr machine) (retCfg next store tracks (index + 1)) =
      some (retCfg next store tracks index) := by
  unfold retCfg baseTape
  simp only [TM1.step]
  rw [TM2to1.tr, TM1.stepAux, Tape.move_right_n_head, Tape.mk'_nth_nat,
    TM2to1.addBottom_nth_succ_fst, TM1.stepAux, Function.iterate_succ',
    Function.comp_apply, Tape.move_right_left]
  rfl

def goTrace (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    List (State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) :=
  (List.range (distance + 1)).map (goCfg k action next store tracks)

def retTrace (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    List (State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) :=
  (List.range (distance + 1)).map (fun index => retCfg next store tracks (distance - index))

theorem go_chain (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (stack : List (Γ k)) (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : tracks.map (proj k) = ListBlank.mk (stack.map some).reverse)
    (distance : Nat) (within : distance ≤ stack.length) :
    (goTrace k action next store tracks distance).IsChain
      (fun before after => TM1.step (TM2to1.tr machine) before = some after) := by
  apply (List.isChain_map _).2
  apply (List.isChain_range_succ _ distance).2
  intro index before
  exact go_step machine k action next store stack tracks represented index (before.trans_le within)

theorem ret_chain (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (retTrace next store tracks distance).IsChain
      (fun before after => TM1.step (TM2to1.tr machine) before = some after) := by
  apply (List.isChain_map _).2
  apply (List.isChain_range_succ _ distance).2
  intro index before
  have subtract : distance - index = (distance - (index + 1)) + 1 := by omega
  rw [subtract]
  exact ret_step machine next store tracks (distance - (index + 1))

omit [DecidableEq K] in
theorem go_length (k : K) (action : TM2to1.StAct K Γ σ k) (next : TM2.Stmt Γ Λ σ)
    (store : σ) (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (goTrace k action next store tracks distance).length = distance + 1 := by
  simp only [goTrace, List.length_map, List.length_range]

omit [DecidableEq K] in
theorem ret_length (next : TM2.Stmt Γ Λ σ) (store : σ)
    (tracks : ListBlank (∀ k, Option (Γ k))) (distance : Nat) :
    (retTrace next store tracks distance).length = distance + 1 := by
  simp only [retTrace, List.length_map, List.length_range]

end PaperProofs.Common.Native.PSTRWordBool.ScannerPaths
