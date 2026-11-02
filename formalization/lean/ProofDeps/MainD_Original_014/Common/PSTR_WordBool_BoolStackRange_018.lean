module

public import Common.PSTR_WordBool_VisitedExtrema_017
public import Mathlib.Data.List.Forall2

/-! Synchronized actual source paths and the SAME old run's head scan.
The extra source HALT supplies the final scan entry. No elapsed-T space
bound or weak Tape-equality argument is used. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.BoolStackRange

open Turing BoolOnStacks BoolStackStep BoolStackRefines BoolStackTrace BoolStackEndpoints
open PaperProofs.Common.Native.RationalControllerComputation (displacement)

variable {states : Nat}

def Geometry (low high position : Int) (state : BoolOnStacks.State states) : Prop :=
  low ≤ position - (state.stk 1).length ∧ position + (state.stk 0).length ≤ high + 1

theorem scan_seed (values : List Int) (position : Int) : position ∈ values.scanl (· + ·) position := by
  cases values <;> simp only [List.scanl_nil, List.scanl_cons, List.mem_cons_self]

theorem preserve_edge (machine : TM0.Machine Bool (Fin (states + 1)))
    (before after : BoolOnStacks.State states) (position low high : Int) (active : before.l = some ())
    (edge : TM2.step (program machine) before = some after)
    (geometry : Geometry low high position before)
    (currentHigh : position ≤ high)
    (nextLow : low ≤ position + displacement machine (representedState before)) :
    Geometry low high (position + displacement machine (representedState before)) after := by
  have endpoints := edge_geometry machine before after position active edge
  constructor
  · rw [endpoints.1]
    exact le_min geometry.1 nextLow
  · rw [endpoints.2]
    exact max_le geometry.2 (by omega)

theorem synchronized_path (machine : TM0.Machine Bool (Fin (states + 1)))
    (start : BoolOnStacks.State states) (oldStart oldFinal : TM0.Cfg Bool (Fin (states + 1)))
    (rest : List (TM0.Cfg Bool (Fin (states + 1)))) (position low high : Int)
    (active : start.l = some ()) (representation : representedState start = oldStart)
    (chain : (oldStart :: rest).IsChain (fun before after => TM0.step machine before = some after))
    (last : (oldStart :: rest).getLast? = some oldFinal) (halt : TM0.step machine oldFinal = none)
    (initialGeometry : Geometry low high position start)
    (bounds : ∀ point ∈ ((oldStart :: rest).map (displacement machine)).scanl (· + ·) position,
      low ≤ point ∧ point ≤ high) :
    ∃ (trace : List (BoolOnStacks.State states)) (final : BoolOnStacks.State states),
      trace.head? = some start ∧
      trace.IsChain (fun before after => TM2.step (program machine) before = some after) ∧
      trace.getLast? = some final ∧ TM2.step (program machine) final = none ∧
      representedState final = oldFinal ∧
      trace.map representedState = (oldStart :: rest) ++ [oldFinal] ∧
      List.Forall₂ (fun state point => Geometry low high point state) trace
        (((oldStart :: rest).map (displacement machine)).scanl (· + ·) position) := by
  have scanEquation : ((oldStart :: rest).map (displacement machine)).scanl (· + ·) position =
      position :: (rest.map (displacement machine)).scanl (· + ·)
        (position + displacement machine oldStart) := by
    rw [List.map_cons, List.scanl_cons]
  have currentBound : low ≤ position ∧ position ≤ high :=
    bounds position (scan_seed _ _)
  have nextBound : low ≤ position + displacement machine oldStart ∧
      position + displacement machine oldStart ≤ high := by
    apply bounds
    rw [scanEquation]
    exact List.mem_cons_of_mem _ (scan_seed _ _)
  induction rest generalizing start oldStart position with
  | nil =>
    have same : oldStart = oldFinal := Option.some.inj last
    have actualHalt : TM0.step machine (representedState start) = none := by
      rw [representation, same]
      exact halt
    obtain ⟨final, edge, done, unchanged⟩ := terminate machine start active actualHalt
    have finalGeometry := preserve_edge machine start final position low high active edge
      initialGeometry currentBound.2 (by simpa only [representation] using nextBound.1)
    have finalRepresentation : representedState final = oldFinal :=
      unchanged.trans (representation.trans same)
    refine ⟨[start, final], final, rfl,
      List.isChain_cons_cons.mpr ⟨edge, List.isChain_singleton _⟩, rfl,
      source_halted machine final done, finalRepresentation, ?_, ?_⟩
    · change [representedState start, representedState final] = [oldStart, oldFinal]
      rw [representation, finalRepresentation]
    · rw [scanEquation]
      rw [List.map_nil, List.scanl_nil]
      constructor
      · exact initialGeometry
      · constructor
        · simpa only [representation] using finalGeometry
        · exact List.Forall₂.nil
  | cons next rest ih =>
    obtain ⟨oldEdge, oldTail⟩ := List.isChain_cons_cons.mp chain
    have actualEdge : TM0.step machine (representedState start) = some next := by
      rw [representation]
      exact oldEdge
    obtain ⟨sourceNext, edge, nextActive, nextRepresentation⟩ := advance machine start next active actualEdge
    have nextGeometry := preserve_edge machine start sourceNext position low high active edge
      initialGeometry currentBound.2 (by simpa only [representation] using nextBound.1)
    have tailBounds : ∀ point ∈ ((next :: rest).map (displacement machine)).scanl (· + ·)
        (position + displacement machine oldStart), low ≤ point ∧ point ≤ high := by
      intro point present
      apply bounds
      rw [scanEquation]
      exact List.mem_cons_of_mem _ present
    obtain ⟨tailTrace, final, tailHead, tailChain, tailLast, finalHalt, finalRepresentation,
      tailMap, tailGeometry⟩ := ih sourceNext next (position + displacement machine oldStart)
        nextActive nextRepresentation oldTail last
        (by simpa only [representation] using nextGeometry) tailBounds
        (by rw [List.map_cons, List.scanl_cons])
        (tailBounds _ (scan_seed _ _))
        (by
          apply tailBounds
          rw [List.map_cons, List.scanl_cons]
          exact List.mem_cons_of_mem _ (scan_seed _ _))
    cases tailTrace with
    | nil => simp at tailHead
    | cons firstSource later =>
      have same : firstSource = sourceNext := Option.some.inj tailHead
      subst firstSource
      refine ⟨start :: sourceNext :: later, final, rfl,
        List.isChain_cons_cons.mpr ⟨edge, tailChain⟩, tailLast, finalHalt,
        finalRepresentation, ?_, ?_⟩
      · change representedState start :: (sourceNext :: later).map representedState =
          oldStart :: (((next :: rest) ++ [oldFinal]))
        rw [representation, tailMap]
      · rw [scanEquation]
        exact List.Forall₂.cons initialGeometry tailGeometry

end PaperProofs.Common.Native.PSTRWordBool.BoolStackRange
