module

public import Paid.PDROC_BitVM_Common_Occupancy_003
public import Common.PSTR_WordBool_ScannerRun_025

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.BitVM.Common

open Turing
open PaperProofs.Common.Native.PSTRWordBool

variable {K Λ σ : Type*}

abbrev BoolTrack (K : Type*) := TM2to1.Γ' K (fun _ : K => Bool)
abbrev BoolTrackState (K Λ σ : Type*) :=
  TM1.Cfg (BoolTrack K) (TM2to1.Λ' K (fun _ : K => Bool) Λ σ) σ

/-- Unpack the EXISTING Mathlib relation, retaining its actual full tape.
This does not choose a fresh representation for an already running state. -/
theorem tracks_of_representation (source : BoolSourceState K Λ σ)
    (configuration : BoolTrackState K Λ σ) (actual : TM2to1.TrCfg source configuration) :
    ∃ tracks : ListBlank (K → Option Bool),
      (∀ k, tracks.map (proj k) = ListBlank.mk ((source.stk k).map some).reverse) ∧
      ScannerRun.compiledCfg source tracks = configuration := by
  cases actual with
  | mk tracks represented => exact ⟨tracks, represented, rfl⟩

theorem representation_of_tracks (source : BoolSourceState K Λ σ)
    (tracks : ListBlank (K → Option Bool))
    (represented : ∀ k, tracks.map (proj k) = ListBlank.mk ((source.stk k).map some).reverse) :
    TM2to1.TrCfg source (ScannerRun.compiledCfg source tracks) := by
  cases source with
  | mk label store slots => exact TM2to1.TrCfg.mk tracks represented

def sourceActionCap (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) : ℕ :=
  support.sup (fun label => ScannerClock.actions (machine label))

/-- Fixed-code polynomial in genuine source path length and input length.
Neither length is an argument read by the compiled machine. -/
def sourceTM1Budget (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) (inputLength sourceLength : ℕ) : ℕ :=
  (2 * sourceActionCap machine support *
    (inputLength + sourcePushCap machine support * sourceLength + sourcePushCap machine support + 1) + 1) *
      sourceLength + 1

def sourceTM1Coefficient (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) : ℕ :=
  2 * sourceActionCap machine support * (sourcePushCap machine support + 1) + 2

theorem sourceTM1Budget_quadratic (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) (inputLength sourceLength : ℕ) :
    sourceTM1Budget machine support inputLength sourceLength ≤
      sourceTM1Coefficient machine support * (inputLength + sourceLength + 1) ^ 2 := by
  let A := sourceActionCap machine support
  let C := sourcePushCap machine support
  let U := inputLength + sourceLength + 1
  have positive : 1 ≤ U := by dsimp [U]; omega
  have lengthBound : sourceLength ≤ U := by dsimp [U]; omega
  have workspace : inputLength + C * sourceLength + C + 1 ≤ (C + 1) * U := by
    calc
      _ ≤ (inputLength + C * sourceLength + C + 1) + (C * inputLength + sourceLength) :=
        Nat.le_add_right _ _
      _ = (C + 1) * U := by dsimp [U]; ring
  have charge : 2 * A * (inputLength + C * sourceLength + C + 1) + 1 ≤
      (2 * A * (C + 1) + 1) * U := by
    calc
      _ ≤ 2 * A * ((C + 1) * U) + 1 := Nat.add_le_add_right (Nat.mul_le_mul_left _ workspace) 1
      _ ≤ 2 * A * ((C + 1) * U) + U := Nat.add_le_add_left positive _
      _ = (2 * A * (C + 1) + 1) * U := by ring
  calc
    sourceTM1Budget machine support inputLength sourceLength =
        (2 * A * (inputLength + C * sourceLength + C + 1) + 1) * sourceLength + 1 := rfl
    _ ≤ ((2 * A * (C + 1) + 1) * U) * U + U ^ 2 :=
      Nat.add_le_add (Nat.mul_le_mul charge lengthBound) (one_le_pow₀ positive)
    _ = sourceTM1Coefficient machine support * (inputLength + sourceLength + 1) ^ 2 := by
      change _ = (2 * A * (C + 1) + 2) * U ^ 2
      ring

variable [DecidableEq K] [Inhabited Λ] [Inhabited σ]

/-- A genuine whole TM2 path yields ONE actual track-TM1 path. All source
workspace and per-label clock qualifications are derived internally from
the same path and fixed closed support. The physical input is still trInit
track data; original raw-Bool I/O adapters and finite alphabet conversion
remain separate actual-code obligations. No full VM is asserted here. -/
theorem tm2_actual_track_trace (machine : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports machine support)
    (inputStack : K) (input : List Bool) (sourceTrace : List (BoolSourceState K Λ σ))
    (sourceFinal : BoolSourceState K Λ σ)
    (first : sourceTrace.head? = some (TM2.init inputStack input))
    (chain : sourceTrace.IsChain (fun before after => TM2.step machine before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) (halt : TM2.step machine sourceFinal = none) :
    ∃ (trace : List (BoolTrackState K Λ σ)) (final : BoolTrackState K Λ σ),
      trace.head? = some (TM1.init (TM2to1.trInit inputStack input)) ∧
      trace.IsChain (fun before after => TM1.step (TM2to1.tr machine) before = some after) ∧
      trace.getLast? = some final ∧ TM1.step (TM2to1.tr machine) final = none ∧
      TM2to1.TrCfg sourceFinal final ∧
      trace.length ≤ sourceTM1Budget machine support input.length sourceTrace.length := by
  cases sourceTrace with
  | nil => simp at first
  | cons start rest =>
    have initial : start = TM2.init inputStack input := Option.some.inj first
    subst start
    let sourceLength := (TM2.init (Γ := fun _ : K => Bool) (Λ := Λ) (σ := σ) inputStack input :: rest).length
    let bound := input.length + sourcePushCap machine support * sourceLength
    have occupancy := source_trace_occupancy machine support closed inputStack input
      (TM2.init inputStack input :: rest) rfl chain
    have initialRepresentation :
        TM2to1.TrCfg (TM2.init (Γ := fun _ : K => Bool) (Λ := Λ) (σ := σ) inputStack input)
          (TM1.init (TM2to1.trInit inputStack input) : BoolTrackState K Λ σ) :=
      TM2to1.trCfg_init (K := K) (Γ := fun _ : K => Bool) (Λ := Λ) (σ := σ) inputStack input
    obtain ⟨tracks, represented, mappedInitial⟩ := tracks_of_representation _ _ initialRepresentation
    have bounded : ∀ state ∈ TM2.init inputStack input :: rest, ∀ k,
        (state.stk k).length ≤ bound := fun state member k => (occupancy state member).2 k
    have counts : ∀ state ∈ TM2.init inputStack input :: rest, ∀ label, state.l = some label →
        ScannerClock.actions (machine label) ≤ sourceActionCap machine support ∧
        AuxWorkspace.pushes (machine label) ≤ sourcePushCap machine support := by
      intro state member label active
      have supported := (occupancy state member).1
      rw [active] at supported
      have inside := Finset.some_mem_insertNone.mp supported
      exact ⟨Finset.le_sup (f := fun q => ScannerClock.actions (machine q)) inside,
        Finset.le_sup (f := fun q => AuxWorkspace.pushes (machine q)) inside⟩
    obtain ⟨changed, posts, changedRep, length, actualChain, actualLast⟩ :=
      ScannerRun.compile_path machine (TM2.init inputStack input) sourceFinal rest tracks represented chain last
        bound (sourceActionCap machine support) (sourcePushCap machine support) bounded counts
    refine ⟨ScannerRun.compiledCfg (TM2.init inputStack input) tracks :: posts,
      ScannerRun.compiledCfg sourceFinal changed, congrArg some mappedInitial, actualChain, actualLast,
      ?_, representation_of_tracks sourceFinal changed changedRep, ?_⟩
    · cases sourceFinal with
      | mk label store slots =>
        cases label with
        | none => rfl
        | some label => cases halt
    · change posts.length + 1 ≤
        (2 * sourceActionCap machine support * (bound + sourcePushCap machine support + 1) + 1) *
          sourceLength + 1
      exact Nat.add_le_add_right (length.trans
        (Nat.mul_le_mul_left _ (by change rest.length ≤ rest.length + 1; omega))) 1

end PDROC.BitVM.Common
