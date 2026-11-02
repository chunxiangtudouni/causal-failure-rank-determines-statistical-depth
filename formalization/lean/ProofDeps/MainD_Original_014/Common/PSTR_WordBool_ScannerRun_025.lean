module

public import Common.PSTR_WordBool_ScannerClock_024
public import Common.PSTR_WordBool_NativeTrace_006

/-! Actual whole-source path compilation. Each macro pays its real initial
normal edge once. Adjacent macros share exactly one endpoint, and the clock
is linear in source transitions times a syntax/workspace polynomial.
Physical internal head ranges and original Bool codecs remain obligations. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.ScannerRun

open Turing ScannerPaths ScannerStatement ScannerClock

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

def compiledCfg (source : TM2.Cfg Γ Λ σ) (tracks : ListBlank (∀ k, Option (Γ k))) :
    ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) :=
  ⟨source.l.map TM2to1.Λ'.normal, source.var, baseTape tracks⟩

theorem step_path (machine : Λ → TM2.Stmt Γ Λ σ) (before after : TM2.Cfg Γ Λ σ)
    (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((before.stk k).map some).reverse)
    (edge : TM2.step machine before = some after) (bound actionBound pushBound : Nat)
    (bounded : ∀ k, (before.stk k).length ≤ bound)
    (counts : ∀ label, before.l = some label →
      actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (posts : List (ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk ((after.stk k).map some).reverse) ∧
      posts.length ≤ 2 * actionBound * (bound + pushBound + 1) + 1 ∧
      (compiledCfg before tracks :: posts).IsChain
        (fun first second => TM1.step (TM2to1.tr machine) first = some second) ∧
      (compiledCfg before tracks :: posts).getLast? = some (compiledCfg after changed) := by
  cases before with
  | mk label store slots =>
    cases label with
    | none => cases edge
    | some label =>
      have endpoint : TM2.stepAux (machine label) store slots = after := Option.some.inj edge
      obtain ⟨changed, trace, changedRep, first, chain, last, length⟩ :=
        actual_path_bound machine (machine label) store slots tracks represented bound bounded
      have static := counts label rfl
      have enlarged : trace.length ≤ 2 * actionBound * (bound + pushBound + 1) + 1 :=
        length.trans (Nat.add_le_add_right
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 static.1)
            (Nat.add_le_add_right (Nat.add_le_add_left static.2 bound) 1)) 1)
      have changedRepAfter : ∀ k, changed.map (proj k) = ListBlank.mk ((after.stk k).map some).reverse := by
        simpa only [endpoint] using changedRep
      have lastAfter : trace.getLast? = some (compiledCfg after changed) := by
        simpa only [representedFinal, compiledCfg, endpoint] using last
      refine ⟨changed, trace, changedRepAfter, enlarged, ?_, ?_⟩
      · apply List.isChain_cons.mpr
        refine ⟨?_, chain⟩
        intro next present
        rw [first] at present
        have same := Option.some.inj (Option.mem_def.mp present)
        subst next
        rfl
      · cases trace with
        | nil => simp at first
        | cons head tail => exact lastAfter

theorem compile_path (machine : Λ → TM2.Stmt Γ Λ σ)
    (before final : TM2.Cfg Γ Λ σ) (rest : List (TM2.Cfg Γ Λ σ))
    (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((before.stk k).map some).reverse)
    (chain : (before :: rest).IsChain (fun first second => TM2.step machine first = some second))
    (last : (before :: rest).getLast? = some final) (bound actionBound pushBound : Nat)
    (bounded : ∀ state ∈ before :: rest, ∀ k, (state.stk k).length ≤ bound)
    (counts : ∀ state ∈ before :: rest, ∀ label, state.l = some label →
      actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (posts : List (ScannerPaths.State (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk ((final.stk k).map some).reverse) ∧
      posts.length ≤ (2 * actionBound * (bound + pushBound + 1) + 1) * rest.length ∧
      (compiledCfg before tracks :: posts).IsChain
        (fun first second => TM1.step (TM2to1.tr machine) first = some second) ∧
      (compiledCfg before tracks :: posts).getLast? = some (compiledCfg final changed) := by
  induction rest generalizing before tracks with
  | nil =>
    have same : before = final := Option.some.inj last
    subst before
    exact ⟨tracks, [], represented, by simp, List.isChain_singleton _, rfl⟩
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    obtain ⟨middle, firstPosts, middleRep, firstLength, firstChain, firstLast⟩ :=
      step_path machine before next tracks represented edge bound actionBound pushBound
        (bounded before List.mem_cons_self) (counts before List.mem_cons_self)
    have tailBounded : ∀ state ∈ next :: rest, ∀ k, (state.stk k).length ≤ bound := by
      intro state present k
      exact bounded state (List.mem_cons_of_mem _ present) k
    have tailCounts : ∀ state ∈ next :: rest, ∀ label, state.l = some label →
        actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound := by
      intro state present label active
      exact counts state (List.mem_cons_of_mem _ present) label active
    obtain ⟨changed, later, changedRep, laterLength, laterChain, laterLast⟩ :=
      ih next middle middleRep tailChain last tailBounded tailCounts
    refine ⟨changed, firstPosts ++ later, changedRep, ?_, ?_, ?_⟩
    · let charge := 2 * actionBound * (bound + pushBound + 1) + 1
      have firstBound : firstPosts.length ≤ charge := firstLength
      have laterBound : later.length ≤ charge * rest.length := laterLength
      rw [List.length_append, List.length_cons]
      change firstPosts.length + later.length ≤ charge * (rest.length + 1)
      exact (Nat.add_le_add firstBound laterBound).trans_eq
        ((Nat.add_comm charge (charge * rest.length)).trans (Nat.mul_succ charge rest.length).symm)
    · exact NativeTrace.join_chain _ _ _ firstLast firstChain laterChain
    · exact (NativeTrace.join_last _ _ _ firstLast).trans laterLast

end PaperProofs.Common.Native.PSTRWordBool.ScannerRun
