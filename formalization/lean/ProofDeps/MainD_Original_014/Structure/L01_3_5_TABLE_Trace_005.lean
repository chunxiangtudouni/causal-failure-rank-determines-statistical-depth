module

public import Structure.L01_3_5_TABLE_RecordNav_Resources_004

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_Trace005

open Turing
open PaperProofs.Common.Native.PSTRWordVM

variable {K : Type*} {Γ : K → Type*} {Λ Ω σ : Type*} [DecidableEq K]

abbrev Cfg := TM2.Cfg Γ Λ σ

theorem stopped_step (source : Λ → TM2.Stmt Γ Λ σ) (before : Cfg (Γ := Γ) (Λ := Λ) (σ := σ))
    (stopped : before.l = none) : TM2.step source before = none := by
  cases before with
  | mk label memory bank =>
      change label = none at stopped
      subst label
      rfl

theorem path_active (source : Λ → TM2.Stmt Γ Λ σ)
    (path : List (Cfg (Γ := Γ) (Λ := Λ) (σ := σ))) (final : Cfg (Γ := Γ) (Λ := Λ) (σ := σ))
    (chain : path.IsChain (fun before after => TM2.step source before = some after))
    (last : path.getLast? = some final) (active : final.l ≠ none) :
    ∀ current ∈ path, current.l ≠ none := by
  induction path with
  | nil => intro current present; cases present
  | cons first rest ih =>
      cases rest with
      | nil =>
          have same : first = final := Option.some.inj last
          subst first
          intro current present
          have same := List.mem_singleton.mp present
          subst current
          exact active
      | cons next rest =>
          obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
          intro current present
          rcases List.mem_cons.mp present with same | later
          · subst current
            intro stopped
            rw [stopped_step source first stopped] at edge
            cases edge
          · exact ih tailChain last current later

theorem proper_not_halt (source : Λ → TM2.Stmt Γ Λ σ)
    (path : List (Cfg (Γ := Γ) (Λ := Λ) (σ := σ))) (final : Cfg (Γ := Γ) (Λ := Λ) (σ := σ))
    (chain : path.IsChain (fun before after => TM2.step source before = some after))
    (last : path.getLast? = some final) (active : final.l ≠ none) :
    ∀ current ∈ path.dropLast, ∀ label, current.l = some label → source label ≠ .halt := by
  induction path with
  | nil => intro current present; cases present
  | cons first rest ih =>
      cases rest with
      | nil => intro current present; cases present
      | cons next rest =>
          obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
          intro current present label position halted
          rw [List.dropLast_cons_cons] at present
          rcases List.mem_cons.mp present with same | later
          · subst current
            have nextActive := path_active source (next :: rest) final tailChain last active next List.mem_cons_self
            have actual : TM2.step source first = some (TM2.stepAux (source label) first.var first.stk) := by
              cases first with
              | mk positionLabel memory bank =>
                  change positionLabel = some label at position
                  subst positionLabel
                  rfl
            rw [halted] at actual
            have same := Option.some.inj (actual.symm.trans edge)
            exact nextActive ((congrArg TM2.Cfg.l same).symm)
          · exact ih tailChain last current later label position halted

theorem chain_on (source target : Λ → TM2.Stmt Γ Λ σ)
    (path : List (Cfg (Γ := Γ) (Λ := Λ) (σ := σ)))
    (chain : path.IsChain (fun before after => TM2.step source before = some after))
    (same : ∀ current ∈ path.dropLast, ∀ label, current.l = some label → target label = source label) :
    path.IsChain (fun before after => TM2.step target before = some after) := by
  induction path with
  | nil => exact List.isChain_nil
  | cons first rest ih =>
      cases rest with
      | nil => exact List.isChain_singleton _
      | cons next rest =>
          obtain ⟨edge,tailChain⟩ := List.isChain_cons_cons.mp chain
          have sameFirst : TM2.step target first = TM2.step source first := by
            cases first with
            | mk label memory bank =>
                cases label with
                | none => rfl
                | some label =>
                    change some (TM2.stepAux (target label) memory bank) = _
                    rw [same _ (by rw [List.dropLast_cons_cons]; exact List.mem_cons_self) label rfl]
                    rfl
          apply List.isChain_cons_cons.mpr
          refine ⟨sameFirst.trans edge,ih tailChain ?_⟩
          intro current member label active
          apply same current _ label active
          rw [List.dropLast_cons_cons]
          exact List.mem_cons_of_mem _ member

structure Part (source : Λ → TM2.Stmt Γ Λ σ)
    (first final : Cfg (Γ := Γ) (Λ := Λ) (σ := σ)) where
  trace : List (Cfg (Γ := Γ) (Λ := Λ) (σ := σ))
  head : trace.head? = some first
  chain : trace.IsChain (fun before after => TM2.step source before = some after)
  last : trace.getLast? = some final

def Part.append {source : Λ → TM2.Stmt Γ Λ σ}
    {first middle next final : Cfg (Γ := Γ) (Λ := Λ) (σ := σ)}
    (front : Part source first middle) (back : Part source next final)
    (edge : TM2.step source middle = some next) : Part source first final where
  trace := front.trace ++ back.trace
  head := by simp only [List.head?_append,front.head,Option.some_or]
  chain := by
    apply List.IsChain.append front.chain back.chain
    intro before beforeLast after afterHead
    simp only [front.last,Option.mem_some_iff] at beforeLast
    simp only [back.head,Option.mem_some_iff] at afterHead
    subst before
    subst after
    exact edge
  last := by simp only [List.getLast?_append,back.last,Option.some_or]

theorem Part.append_length {source : Λ → TM2.Stmt Γ Λ σ}
    {first middle next final : Cfg (Γ := Γ) (Λ := Λ) (σ := σ)}
    (front : Part source first middle) (back : Part source next final)
    (edge : TM2.step source middle = some next) :
    (front.append back edge).trace.length = front.trace.length + back.trace.length :=
  List.length_append

end PaperProofs.Common.Native.L01_3_5_TABLE_Trace005
