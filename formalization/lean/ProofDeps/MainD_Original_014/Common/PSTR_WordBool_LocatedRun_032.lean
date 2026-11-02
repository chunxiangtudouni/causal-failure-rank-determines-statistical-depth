module

public import Common.PSTR_WordBool_LocatedStatement_031
public import Common.PSTR_WordBool_ScannerRun_025

/-! ONE actual whole Gamma scanner run with coupled clock and coordinates.
All macro boundaries are at the real bottom; each initial normal edge is
charged and adjacent chunks identify exactly one shared located endpoint. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.LocatedRun

open Turing ScannerPaths ScannerStatement ScannerDisplacement

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

def compiledPoint (source : TM2.Cfg Γ Λ σ) (tracks : ListBlank (∀ k, Option (Γ k))) :
    LocatedScanner.Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) :=
  (ScannerRun.compiledCfg source tracks, 0)

theorem step_path (machine : Λ → TM2.Stmt Γ Λ σ) (before after : TM2.Cfg Γ Λ σ)
    (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((before.stk k).map some).reverse)
    (edge : TM2.step machine before = some after) (bound actionBound pushBound : Nat)
    (bounded : ∀ k, (before.stk k).length ≤ bound)
    (counts : ∀ label, before.l = some label →
      ScannerClock.actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (posts : List (LocatedScanner.Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk ((after.stk k).map some).reverse) ∧
      posts.length ≤ 2 * actionBound * (bound + pushBound + 1) + 1 ∧
      (compiledPoint before tracks :: posts).IsChain (LocatedScanner.Step machine) ∧
      (compiledPoint before tracks :: posts).getLast? = some (compiledPoint after changed) ∧
      ∀ point ∈ compiledPoint before tracks :: posts,
        0 ≤ point.2 ∧ point.2 ≤ ((bound + pushBound : Nat) : Int) := by
  cases before with
  | mk label store slots =>
    cases label with
    | none => cases edge
    | some label =>
      have endpoint : TM2.stepAux (machine label) store slots = after := Option.some.inj edge
      obtain ⟨changed, trace, changedRep, first, chain, last, _length, time, coordinates⟩ :=
        LocatedStatement.actual_path machine (machine label) store slots tracks represented bound bounded
      have static := counts label rfl
      have enlarged : trace.length ≤ 2 * actionBound * (bound + pushBound + 1) + 1 :=
        time.trans (Nat.add_le_add_right
          (Nat.mul_le_mul (Nat.mul_le_mul_left 2 static.1)
            (Nat.add_le_add_right (Nat.add_le_add_left static.2 bound) 1)) 1)
      have changedRepAfter : ∀ k, changed.map (proj k) = ListBlank.mk ((after.stk k).map some).reverse := by
        simpa only [endpoint] using changedRep
      have lastAfter : trace.getLast? = some (compiledPoint after changed) := by
        simpa only [representedFinal, compiledPoint, ScannerRun.compiledCfg, endpoint] using last
      refine ⟨changed, trace, changedRepAfter, enlarged, ?_, ?_, ?_⟩
      · apply List.isChain_cons.mpr
        refine ⟨?_, chain⟩
        intro next present
        rw [first] at present
        have same := Option.some.inj (Option.mem_def.mp present)
        subst next
        refine ⟨rfl, ?_⟩
        change (0 : Int) = 0 + StatementDisplacement.netMove
          (TM2to1.trNormal (machine label)) store (baseTape tracks)
        simp only [normal_zero, Int.add_zero]
      · cases trace with
        | nil => simp at first
        | cons head tail => exact lastAfter
      · intro point present
        rcases List.mem_cons.mp present with same | later
        · subst point
          change (0 : Int) ≤ 0 ∧ 0 ≤ ((bound + pushBound : Nat) : Int)
          constructor <;> omega
        · have within := coordinates point later
          have larger := Nat.add_le_add_left static.2 bound
          constructor <;> omega

theorem compile_path (machine : Λ → TM2.Stmt Γ Λ σ)
    (before final : TM2.Cfg Γ Λ σ) (rest : List (TM2.Cfg Γ Λ σ))
    (tracks : ListBlank (∀ k, Option (Γ k)))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((before.stk k).map some).reverse)
    (chain : (before :: rest).IsChain (fun first second => TM2.step machine first = some second))
    (last : (before :: rest).getLast? = some final) (bound actionBound pushBound : Nat)
    (bounded : ∀ state ∈ before :: rest, ∀ k, (state.stk k).length ≤ bound)
    (counts : ∀ state ∈ before :: rest, ∀ label, state.l = some label →
      ScannerClock.actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound) :
    ∃ (changed : ListBlank (∀ k, Option (Γ k)))
      (posts : List (LocatedScanner.Located (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))),
      (∀ k, changed.map (proj k) = ListBlank.mk ((final.stk k).map some).reverse) ∧
      posts.length ≤ (2 * actionBound * (bound + pushBound + 1) + 1) * rest.length ∧
      (compiledPoint before tracks :: posts).IsChain (LocatedScanner.Step machine) ∧
      (compiledPoint before tracks :: posts).getLast? = some (compiledPoint final changed) ∧
      ∀ point ∈ compiledPoint before tracks :: posts,
        0 ≤ point.2 ∧ point.2 ≤ ((bound + pushBound : Nat) : Int) := by
  induction rest generalizing before tracks with
  | nil =>
    have same : before = final := Option.some.inj last
    subst before
    refine ⟨tracks, [], represented, by simp, List.isChain_singleton _, rfl, ?_⟩
    intro point present
    have same := List.mem_singleton.mp present
    subst point
    change (0 : Int) ≤ 0 ∧ 0 ≤ ((bound + pushBound : Nat) : Int)
    constructor <;> omega
  | cons next rest ih =>
    obtain ⟨edge, tailChain⟩ := List.isChain_cons_cons.mp chain
    obtain ⟨middle, firstPosts, middleRep, firstLength, firstChain, firstLast, firstRange⟩ :=
      step_path machine before next tracks represented edge bound actionBound pushBound
        (bounded before List.mem_cons_self) (counts before List.mem_cons_self)
    have tailBounded : ∀ state ∈ next :: rest, ∀ k, (state.stk k).length ≤ bound := by
      intro state present k
      exact bounded state (List.mem_cons_of_mem _ present) k
    have tailCounts : ∀ state ∈ next :: rest, ∀ label, state.l = some label →
        ScannerClock.actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound := by
      intro state present label active
      exact counts state (List.mem_cons_of_mem _ present) label active
    obtain ⟨changed, later, changedRep, laterLength, laterChain, laterLast, laterRange⟩ :=
      ih next middle middleRep tailChain last tailBounded tailCounts
    refine ⟨changed, firstPosts ++ later, changedRep, ?_, ?_, ?_, ?_⟩
    · let charge := 2 * actionBound * (bound + pushBound + 1) + 1
      have firstBound : firstPosts.length ≤ charge := firstLength
      have laterBound : later.length ≤ charge * rest.length := laterLength
      rw [List.length_append, List.length_cons]
      change firstPosts.length + later.length ≤ charge * (rest.length + 1)
      exact (Nat.add_le_add firstBound laterBound).trans_eq
        ((Nat.add_comm charge (charge * rest.length)).trans (Nat.mul_succ charge rest.length).symm)
    · exact NativeTrace.join_chain _ _ _ firstLast firstChain laterChain
    · exact (NativeTrace.join_last _ _ _ firstLast).trans laterLast
    · intro point present
      rcases List.mem_cons.mp present with same | laterPoint
      · subst point
        exact firstRange _ List.mem_cons_self
      · rcases List.mem_append.mp laterPoint with first | later
        · exact firstRange point (List.mem_cons_of_mem _ first)
        · exact laterRange point (List.mem_cons_of_mem _ later)

end PaperProofs.Common.Native.PSTRWordBool.LocatedRun
