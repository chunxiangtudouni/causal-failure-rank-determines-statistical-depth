module

public import RootB236_RiskFold_Widths001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB236.RiskFold

open Turing
open PaperProofs.Common.Native.PSTRWordBool

variable {Λ σ : Type*}
abbrev Statement (Λ σ : Type*) := TM2.Stmt RatInput.Alphabet Λ σ
abbrev State (Λ σ : Type*) := TM2.Cfg RatInput.Alphabet Λ σ

structure Part (source : Λ → Statement Λ σ) (before final : State Λ σ) where
  trace : List (State Λ σ)
  first : trace.head?=some before
  chain : trace.IsChain (fun a b => TM2.step source a=some b)
  last : trace.getLast?=some final

def Part.edge {source : Λ → Statement Λ σ} {before final : State Λ σ}
    (step : TM2.step source before=some final) : Part source before final :=
  ⟨[before,final],rfl,List.isChain_cons_cons.mpr ⟨step,List.isChain_singleton _⟩,rfl⟩

def Part.append {source : Λ → Statement Λ σ} {before middle next final : State Λ σ}
    (front : Part source before middle) (back : Part source next final)
    (bridge : TM2.step source middle=some next) : Part source before final where
  trace := front.trace ++ back.trace
  first := by simp only [List.head?_append,front.first,Option.some_or]
  last := by simp only [List.getLast?_append,back.last,Option.some_or]
  chain := by
    apply List.IsChain.append front.chain back.chain
    intro left leftLast right rightFirst
    simp only [front.last,Option.mem_some_iff] at leftLast
    simp only [back.first,Option.mem_some_iff] at rightFirst
    subst left
    subst right
    exact bridge

theorem Part.join {source : Λ → Statement Λ σ} {before middle final : State Λ σ}
    (front : Part source before middle) (back : Part source middle final) :
    ∃ all : Part source before final, all.trace.length ≤ front.trace.length+back.trace.length := by
  rcases back with ⟨trace,first,chain,last⟩
  cases trace with
  | nil => cases first
  | cons head rest =>
    have equal : head=middle := Option.some.inj first
    subst head
    cases rest with
    | nil =>
      have equal : middle=final := Option.some.inj last
      subst final
      exact ⟨front,Nat.le_add_right _ _⟩
    | cons next later =>
      obtain ⟨step,tailChain⟩ := List.isChain_cons_cons.mp chain
      let tailPart : Part source next final := ⟨next::later,rfl,tailChain,last⟩
      refine ⟨front.append tailPart step,?_⟩
      change (front.trace ++ next::later).length ≤ _
      simp only [List.length_append,List.length_cons]
      omega

theorem chain_switch (source target : Λ → Statement Λ σ) (trace : List (State Λ σ))
    (chain : trace.IsChain (fun a b => TM2.step source a=some b))
    (same : ∀ current∈trace.dropLast, ∀ point, current.l=some point → target point=source point) :
    trace.IsChain (fun a b => TM2.step target a=some b) := by
  induction trace with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
    cases rest with
    | nil => exact List.isChain_singleton _
    | cons next later =>
      obtain ⟨step,tailChain⟩ := List.isChain_cons_cons.mp chain
      refine List.isChain_cons_cons.mpr ⟨?_,ih tailChain ?_⟩
      · cases first with
        | mk position memory bank =>
          cases position with
          | none => cases step
          | some point =>
            change some (TM2.stepAux (target point) memory bank)=_
            rw [same _ (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) point rfl]
            exact step
      · intro current present point selected
        apply same current _ point selected
        rw [List.dropLast_cons_cons]
        exact List.mem_cons_of_mem _ present

end RootB236.RiskFold
