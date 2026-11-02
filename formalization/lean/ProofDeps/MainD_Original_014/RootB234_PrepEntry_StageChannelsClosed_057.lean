module

public import RootB234_PrepEntry_StageChannelsCode_056

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepEntry.StageChannels

open Turing PaperProofs.Common PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open PSTRWordVM B23_4_RatWordPrep

def LoopPoint : Channels.Label → Prop
  | .prelude _ | .build _ => False
  | .round _ | .read _ | .move _ | .done => True

instance (point : Channels.Label) : Decidable (LoopPoint point) := by
  cases point <;> dsimp only [LoopPoint] <;> infer_instance

def loopLabels : Finset Channels.Label := Finset.univ.filter LoopPoint

theorem mem_loop (point : Channels.Label) : point∈loopLabels ↔ LoopPoint point := by simp only [loopLabels,Finset.mem_filter,Finset.mem_univ,true_and]

private theorem tagged_supports {Λ σ : Type*} (rename : Λ → Channels.Label)
    (closed : ∀ point,LoopPoint (rename point)) (body : TM2.Stmt RatInput.Alphabet Λ σ) :
    TM2.SupportsStmt loopLabels (LabelMap.statement rename body) := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto destination => intro memory; exact (mem_loop _).mpr (closed (destination memory))
  | halt => trivial

private theorem round_closed (point : RootB234.RuntimeCounter.Round.Label) : LoopPoint (Channels.roundLabel point) := by
  unfold Channels.roundLabel
  split_ifs <;> trivial

private theorem read_closed (point : RawGetter.Label) : LoopPoint (Channels.readLabel point) := by
  unfold Channels.readLabel
  split_ifs <;> trivial

private theorem move_closed (point : RootB234.RatPacketTransport.Label) : LoopPoint (Channels.moveLabel point) := by
  unfold Channels.moveLabel
  split_ifs <;> trivial

theorem loop_supports_stmt {D : Type*} (point : Channels.Label) (allowed : LoopPoint point) :
    TM2.SupportsStmt loopLabels (Channels.program (C := D) .halt point) := by
  cases point with
  | prelude _ | build _ => exact False.elim allowed
  | round point => exact tagged_supports Channels.roundLabel round_closed _
  | read point => exact tagged_supports Channels.readLabel read_closed _
  | move point => exact tagged_supports Channels.moveLabel move_closed _
  | done => trivial

/-- This is the current-round SUBROUTINE invariant, not a replacement for
the real source's literal default entry. The local inhabited witness is
used only to apply Mathlib's support lemma from the supplied round0 node. -/
theorem loop_closed {D : Type*} (run : List (Channels.State D)) (before : Channels.State D)
    (first : run.head?=some before)
    (chain : run.IsChain (fun a b => TM2.step (Channels.program .halt) a=some b))
    (active : before.l=some (.round 0)) :
    ∀ current∈run,∀ point,current.l=some point→LoopPoint point := by
  let : Inhabited Channels.Label:=⟨.round 0⟩
  have support : TM2.Supports (Channels.program (C := D) .halt) loopLabels :=
    ⟨(mem_loop _).mpr trivial,fun point member => loop_supports_stmt point ((mem_loop _).mp member)⟩
  have start : before.l∈Finset.insertNone loopLabels := by
    rw [active]
    exact Finset.some_mem_insertNone.mpr ((mem_loop _).mpr trivial)
  have all : ∀ (path : List (Channels.State D)) (initial : Channels.State D),
      path.head?=some initial→path.IsChain (fun a b => TM2.step (Channels.program .halt) a=some b)→
      initial.l∈Finset.insertNone loopLabels→
      ∀ current∈path,current.l∈Finset.insertNone loopLabels := by
    intro path
    induction path with
    | nil => intro initial head linked member current present; cases present
    | cons initial rest ih =>
      intro before head linked member
      have same : initial=before := Option.some.inj head
      subst initial
      cases rest with
      | nil =>
        intro current present
        have same:=List.mem_singleton.mp present
        subst current
        exact member
      | cons next rest =>
        obtain ⟨edge,tailChain⟩:=List.isChain_cons_cons.mp linked
        have nextMember:=TM2.step_supports (Channels.program .halt) support (c := before) (c' := next)
          (by simp [edge]) member
        intro current present
        rcases List.mem_cons.mp present with rfl|later
        · exact member
        · exact ih next rfl tailChain nextMember current later
  intro current present point selected
  have member:=all run before first chain start current present
  rw [selected] at member
  exact (mem_loop _).mp (Finset.some_mem_insertNone.mp member)

theorem loopSource_eq {C : Type*} (caller : Channels.Statement (StageFront.Store C))
    (point : Channels.Label) (allowed : LoopPoint point) :
    loopSource caller point=Channels.program caller point := by
  cases point with
  | prelude _ | build _ => exact False.elim allowed
  | round _ | read _ | move _ | done => rfl

end RootB234.PrepEntry.StageChannels
