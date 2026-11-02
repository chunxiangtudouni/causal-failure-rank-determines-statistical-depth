module

public import Common.PSTR_WordBool_RawOutput_Source001
public import Common.PSTR_WordBool_AlphabetTrace_008

/-! Actual Bool-native execution of the fixed cleanup source. The source
path starts on ALL sixteen represented stacks, not on a one-stack input.
Only the proof reifies a finite tape to use the existing native compiler. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace PaperProofs.Common.Native.PSTRWordBool.RawOutput

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PaperProofs.Common.Native.RationalControllerComputation.PSTRTMSeq005

abbrev Tracks := ListBlank (Fin 16 → Option Bool)

def encodedTape (tracks : Tracks) : Tape Bool :=
  TM1to1.trTape (FiniteTrackCodec.encode_default 16) (ScannerPaths.baseTape tracks)

def represented (bank : Stacks) (tracks : Tracks) : Prop :=
  ∀ slot, tracks.map (proj slot) = ListBlank.mk ((bank slot).map some).reverse

noncomputable def cleanupStates : Nat := (TM2Native.nativeSupport sourceMachine Finset.univ).card
noncomputable def cleanupMachine : Machine cleanupStates := TM2Native.nativeMachine sourceMachine Finset.univ
noncomputable def cleanupCoefficient : Nat := 1024*(TM2Native.nativeBudget sourceMachine Finset.univ+1)

noncomputable def cleanupHalt : Fin (cleanupStates+1) :=
  PSTRSymbolicRelabel.finiteLabels (TM2Native.nativeSupport sourceMachine Finset.univ) (none,false)

private def bottomRows (rows : List (Fin 16 → Option Bool)) : List (FiniteTrackCodec.Track 16) :=
  match rows with
  | [] => [(true,default)]
  | row :: later => (true,row) :: later.map (fun row => (false,row))

private theorem base_mk (rows : List (Fin 16 → Option Bool)) :
    ScannerPaths.baseTape (ListBlank.mk rows) = Tape.mk₁ (bottomRows rows) := by
  cases rows <;>
    simp [ScannerPaths.baseTape, TM2to1.addBottom, bottomRows, Tape.mk₁, Tape.mk₂] <;> rfl

private theorem represented_unique (bank : Stacks) (first second : Tracks)
    (hf : represented bank first) (hs : represented bank second) : first=second := by
  apply ListBlank.ext
  intro index
  funext slot
  have same := congrArg (fun tape => tape.nth index) ((hf slot).trans (hs slot).symm)
  simpa only [ListBlank.nth_map, proj] using same

private theorem singleton_bank (bank : Stacks) :
    clearFrom 0 bank = Function.update (fun _ : Fin 16 => ([] : List Bool)) 0 (bank 0) := by
  funext slot
  by_cases same : slot=0
  · subst slot; simp [clearFrom]
  · rw [clear_other bank slot same, Function.update_of_ne same]

/-- After the paid cleanup every physical row is exactly the existing
single-stack codec, including its real bottom marker and genuine blank end. -/
theorem singleton_tape (bank : Stacks) (tracks : Tracks)
    (rep : represented (clearFrom 0 bank) tracks) :
    encodedTape tracks = Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (bank 0)) := by
  let start := TM2.init (Γ := fun _ : Fin 16 => Bool) (Λ := Fin 16) (σ := Bool) 0 (bank 0)
  obtain ⟨canonical, canonicalRep, canonicalCfg⟩ := TM2Native.represented_cfg start
    (TM1.init (Γ := FiniteTrackCodec.Track 16)
      (Λ := TM2Native.GammaLabel 16 (Fin 16) Bool) (σ := Bool)
      (TM2to1.trInit (Γ := fun _ : Fin 16 => Bool) 0 (bank 0)))
    (TM2to1.trCfg_init (Γ := fun _ : Fin 16 => Bool) (Λ := Fin 16) (σ := Bool) 0 (bank 0))
  have actualRep : represented (clearFrom 0 bank) canonical := by
    simpa only [represented, start, TM2.init, singleton_bank] using canonicalRep
  have same := represented_unique (clearFrom 0 bank) tracks canonical rep actualRep
  rw [same]
  have tape := congrArg (fun state => state.Tape) canonicalCfg
  change ScannerPaths.baseTape canonical = Tape.mk₁ (TM2to1.trInit 0 (bank 0)) at tape
  unfold encodedTape
  rw [tape, TM2Native.encode_tape]
  rfl

private theorem cleanup_list (bank : Stacks) (rows : List (Fin 16 → Option Bool))
    (rep : represented bank (ListBlank.mk rows)) :
    ∃ trace final, RunsFrom cleanupMachine
      ⟨0, encodedTape (ListBlank.mk rows)⟩ trace final ∧
      final.q=cleanupHalt ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (bank 0)) ∧
      trace.length ≤ cleanupCoefficient*(weight bank)^2 := by
  let input := (bottomRows rows).flatMap (fun row => (FiniteTrackCodec.encode row).toList)
  let before := sourceCfg 0 (by omega) false bank
  let finish := sourceFinal (clearFrom 0 bank)
  let W := weight bank
  have positive : 1 ≤ W := by dsimp [W,weight]; omega
  obtain ⟨sourceRest, sourceChain, sourceLast, sourceClock, sourceBound⟩ := source_path bank
  have stackBound : ∀ state ∈ before :: sourceRest, ∀ slot, (state.stk slot).length ≤ W := by
    intro state present slot
    exact (sourceBound state present slot).trans (Nat.le_of_lt (slot_length_lt_weight bank slot))
  have counts : ∀ state ∈ before :: sourceRest, ∀ label, state.l=some label →
      ScannerClock.actions (sourceMachine label) ≤ 1 ∧ AuxWorkspace.pushes (sourceMachine label) ≤ 0 := by
    intro _ _ label _
    exact ⟨(source_counts label).1, (source_counts label).2.le⟩
  obtain ⟨changed, gammaPosts, changedRep, gammaLength, gammaChain, gammaLast⟩ :=
    ScannerRun.compile_path sourceMachine before finish sourceRest (ListBlank.mk rows) rep
      sourceChain sourceLast W 1 0 stackBound counts
  let gammaStart := ScannerRun.compiledCfg before (ListBlank.mk rows)
  let gammaFinish := ScannerRun.compiledCfg finish changed
  have gammaBudget : ∀ state ∈ gammaStart :: gammaPosts, ∀ label, state.l=some label →
      AlphabetClock.writes (TM2Native.gammaMachine sourceMachine label)+1 ≤ 2 := by
    intro _ _ label _
    exact (TM2Native.scanner_bounds sourceMachine label).1
  obtain ⟨boolPosts, boolLength, boolChain, boolLast⟩ :=
    AlphabetTrace.compile_path FiniteTrackCodec.encode FiniteTrackCodec.decode
      (FiniteTrackCodec.encode_default 16) FiniteTrackCodec.decode_encode
      (TM2Native.gammaMachine sourceMachine) 2 gammaStart gammaFinish gammaPosts
      gammaChain gammaLast gammaBudget
  let boolStart := TM1to1.trCfg FiniteTrackCodec.encode (FiniteTrackCodec.encode_default 16) gammaStart
  let boolFinish := TM1to1.trCfg FiniteTrackCodec.encode (FiniteTrackCodec.encode_default 16) gammaFinish
  have initialTape : encodedTape (ListBlank.mk rows) = Tape.mk₁ input := by
    unfold encodedTape
    rw [base_mk, TM2Native.encode_tape]
  have initial : boolStart=TM1.init input := by
    change (⟨some (.normal (.normal (phaseLabel 0 (by omega)))),false,
      encodedTape (ListBlank.mk rows)⟩ : TM1.Cfg Bool (TM2Native.BoolLabel 16 (Fin 16) Bool) Bool)=_
    rw [initialTape]
    rfl
  have boolFirst : (boolStart :: boolPosts).head?=some (TM1.init input) := congrArg some initial
  have boolHalt : TM1.step (TM2Native.boolMachine sourceMachine) boolFinish=none := rfl
  obtain ⟨native, nativeFirst, nativeChain, nativeLast, nativeHalt, nativeLength⟩ :=
    SupportClock.actual_native_trace (TM2Native.boolMachine sourceMachine)
      (TM2Native.boolSupport sourceMachine Finset.univ)
      (TM2Native.bool_supports sourceMachine Finset.univ source_closed)
      input (boolStart :: boolPosts) boolFinish boolFirst boolChain boolLast boolHalt
  let nativeFinal := TM1to0.trCfg (TM2Native.boolMachine sourceMachine) boolFinish
  have run := PSTRSymbolicRelabel.finite_runs
    (TM1to0.tr (TM2Native.boolMachine sourceMachine))
    (TM2Native.nativeSupport sourceMachine Finset.univ)
    (TM2Native.native_supports sourceMachine Finset.univ source_closed)
    input native nativeFinal nativeFirst nativeChain nativeLast nativeHalt
  refine ⟨native.map (PSTRSymbolicRelabel.relabelCfg
    (PSTRSymbolicRelabel.finiteLabels (TM2Native.nativeSupport sourceMachine Finset.univ))),
      PSTRSymbolicRelabel.relabelCfg
        (PSTRSymbolicRelabel.finiteLabels (TM2Native.nativeSupport sourceMachine Finset.univ)) nativeFinal,
    ?_, rfl, ?_, ?_⟩
  · rw [initialTape]
    exact ⟨run.1,run.2.1,run.2.2.1,run.2.2.2.1⟩
  · exact singleton_tape bank changed changedRep
  · have gammaBound : gammaPosts.length ≤ 80*W^2 := by
      have times := Nat.mul_le_mul_left (2*(W+1)+1) sourceClock
      dsimp [W] at times ⊢
      simp only [Nat.mul_one, Nat.add_zero] at gammaLength
      nlinarith
    have boolBound : (boolStart :: boolPosts).length ≤ 161*W^2 := by
      simp only [List.length_cons]
      nlinarith
    have times := Nat.mul_le_mul_left (TM2Native.nativeBudget sourceMachine Finset.univ) boolBound
    have square : 1 ≤ W^2 := by nlinarith
    simp only [List.length_map]
    change native.length ≤ 1024*(TM2Native.nativeBudget sourceMachine Finset.univ+1)*W^2
    change native.length ≤ TM2Native.nativeBudget sourceMachine Finset.univ *
      (boolStart :: boolPosts).length+1 at nativeLength
    nlinarith [Nat.zero_le (TM2Native.nativeBudget sourceMachine Finset.univ*W^2)]

/-- No empty-other-stack promise: the fixed machine actually erases them.
Its clock depends on current occupied stack sizes and never on elapsed F. -/
theorem cleanup_contract (bank : Stacks) (tracks : Tracks) (rep : represented bank tracks) :
    ∃ trace final, RunsFrom cleanupMachine ⟨0,encodedTape tracks⟩ trace final ∧
      final.q=cleanupHalt ∧
      final.Tape=Tape.mk₁ (FiniteTrackCodec.encodedInput (0 : Fin 16) (bank 0)) ∧
      trace.length ≤ cleanupCoefficient*(weight bank)^2 := by
  revert rep
  exact tracks.induction_on (fun rows rep => cleanup_list bank rows rep)

end PaperProofs.Common.Native.PSTRWordBool.RawOutput
