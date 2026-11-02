module

public import Common.PSTR_WordBool_LocatedSpace_039
public import Common.PSTR_WordBool_LocatedRun_032
public import Common.PSTR_WordBool_FiniteTrackCodec_030
public import Common.PSTR_WordBool_SupportClock_007

/-! The actual fixed-stack Bool compiler. Fixed source support, finite
store, track encoding and native syntax constants are chosen before input.
No original raw-input adapter or output decoder is supplied here. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.TM2Native

open Turing
open PaperProofs.Common.Native.RationalControllerComputation

abbrev StackAlphabet (count : Nat) : Fin count → Type := fun _ => Bool
abbrev GammaLabel (count : Nat) (Λ σ : Type*) := TM2to1.Λ' (Fin count) (StackAlphabet count) Λ σ
abbrev BoolLabel (count : Nat) (Λ σ : Type*) := TM1to1.Λ' (FiniteTrackCodec.Track count) (GammaLabel count Λ σ) σ

variable {count : Nat} {Λ σ : Type*} [Inhabited Λ] [Inhabited σ] [Fintype σ]

def gammaMachine (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) :
    GammaLabel count Λ σ → TM1.Stmt (FiniteTrackCodec.Track count) (GammaLabel count Λ σ) σ :=
  TM2to1.tr machine

def boolMachine (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) :
    BoolLabel count Λ σ → TM1.Stmt Bool (BoolLabel count Λ σ) σ :=
  TM1to1.tr FiniteTrackCodec.encode FiniteTrackCodec.decode (gammaMachine machine)

noncomputable def gammaSupport (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) (support : Finset Λ) :
    Finset (GammaLabel count Λ σ) := TM2to1.trSupp machine support

noncomputable def boolSupport (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) (support : Finset Λ) :
    Finset (BoolLabel count Λ σ) := TM1to1.trSupp (gammaMachine machine) (gammaSupport machine support)

noncomputable def nativeSupport (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) (support : Finset Λ) :
    Finset (TM1to0.Λ' (boolMachine machine)) := TM1to0.trStmts (boolMachine machine) (boolSupport machine support)

noncomputable def nativeBudget (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) (support : Finset Λ) : Nat :=
  SupportClock.clock (boolMachine machine) (boolSupport machine support)

noncomputable def nativeMachine (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) (support : Finset Λ) :
    Machine (nativeSupport machine support).card :=
  PSTRSymbolicRelabel.finiteMachine (TM1to0.tr (boolMachine machine)) (nativeSupport machine support)

omit [Inhabited σ] [Fintype σ] in
theorem bool_supports (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) (support : Finset Λ)
    (closed : TM2.Supports machine support) : TM1.Supports (boolMachine machine) (boolSupport machine support) :=
  TM1to1.tr_supports FiniteTrackCodec.encode FiniteTrackCodec.decode (gammaMachine machine)
    (TM2to1.tr_supports machine closed)

theorem native_supports (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ) (support : Finset Λ)
    (closed : TM2.Supports machine support) :
    TM0.Supports (TM1to0.tr (boolMachine machine)) (nativeSupport machine support : Set (TM1to0.Λ' (boolMachine machine))) :=
  TM1to0.tr_supports (boolMachine machine) (bool_supports machine support closed)

omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
theorem normal_bounds (statement : TM2.Stmt (StackAlphabet count) Λ σ) :
    AlphabetClock.writes (TM2to1.trNormal statement) = 0 ∧
      AlphabetPrefix.motionRadius (TM2to1.trNormal statement) = 0 := by
  induction statement with
  | push slot value tail _ih => exact ⟨rfl, rfl⟩
  | peek slot value tail _ih => exact ⟨rfl, rfl⟩
  | pop slot value tail _ih => exact ⟨rfl, rfl⟩
  | load update tail ih => exact ih
  | branch test yes no ihYes ihNo =>
    constructor
    · change AlphabetClock.writes (TM2to1.trNormal yes) + AlphabetClock.writes (TM2to1.trNormal no) = 0
      rw [ihYes.1, ihNo.1]
    · change AlphabetPrefix.motionRadius (TM2to1.trNormal yes) + AlphabetPrefix.motionRadius (TM2to1.trNormal no) = 0
      rw [ihYes.2, ihNo.2]
  | goto target => exact ⟨rfl, rfl⟩
  | halt => exact ⟨rfl, rfl⟩

omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
theorem scanner_bounds (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ)
    (label : GammaLabel count Λ σ) :
    AlphabetClock.writes (gammaMachine machine label) + 1 ≤ 2 ∧
      AlphabetPrefix.motionRadius (gammaMachine machine label) ≤ 3 := by
  cases label with
  | normal label =>
    change AlphabetClock.writes (TM2to1.trNormal (machine label)) + 1 ≤ 2 ∧
      AlphabetPrefix.motionRadius (TM2to1.trNormal (machine label)) ≤ 3
    rw [(normal_bounds (machine label)).1, (normal_bounds (machine label)).2]
    exact ⟨by decide, by decide⟩
  | go slot action next =>
    cases action with
    | push value =>
      change 2 ≤ 2 ∧ 2 ≤ 3
      exact ⟨le_rfl, by decide⟩
    | peek value =>
      change 1 ≤ 2 ∧ 3 ≤ 3
      exact ⟨by decide, le_rfl⟩
    | pop value =>
      change 2 ≤ 2 ∧ 2 ≤ 3
      exact ⟨le_rfl, by decide⟩
  | ret next =>
    change AlphabetClock.writes (TM2to1.trNormal next) + 0 + 1 ≤ 2 ∧
      AlphabetPrefix.motionRadius (TM2to1.trNormal next) + 1 ≤ 3
    rw [(normal_bounds next).1, (normal_bounds next).2]
    exact ⟨by decide, by decide⟩

omit [Inhabited Λ] [Inhabited σ] [Fintype σ] in
theorem represented_cfg (source : TM2.Cfg (StackAlphabet count) Λ σ)
    (target : TM1.Cfg (FiniteTrackCodec.Track count) (GammaLabel count Λ σ) σ)
    (representation : TM2to1.TrCfg source target) :
    ∃ tracks, (∀ slot, tracks.map (proj slot) = ListBlank.mk ((source.stk slot).map some).reverse) ∧
      ScannerRun.compiledCfg source tracks = target := by
  cases representation with
  | mk tracks represented => exact ⟨tracks, represented, rfl⟩

theorem encode_tape (rows : List (FiniteTrackCodec.Track count)) :
    TM1to1.trTape (FiniteTrackCodec.encode_default count) (Tape.mk₁ rows) =
      Tape.mk₁ (rows.flatMap (fun row => (FiniteTrackCodec.encode row).toList)) := by
  rw [Tape.mk₁, Tape.mk₂, TM1to1.trTape_mk']
  unfold TM1to1.trTape'
  simp only [ListBlank.flatMap_mk, List.flatMap_nil]
  rfl

omit [Fintype σ] in
theorem mapped_initial (slot : Fin count) (input : List Bool) :
    TM1to1.trCfg FiniteTrackCodec.encode (FiniteTrackCodec.encode_default count)
      (TM1.init (Γ := FiniteTrackCodec.Track count) (Λ := GammaLabel count Λ σ) (σ := σ)
        (TM2to1.trInit (Γ := StackAlphabet count) slot input)) =
      TM1.init (Γ := Bool) (Λ := BoolLabel count Λ σ) (σ := σ) (FiniteTrackCodec.encodedInput slot input) := by
  change (⟨some (.normal default), default, TM1to1.trTape (FiniteTrackCodec.encode_default count)
    (Tape.mk₁ (TM2to1.trInit (Γ := StackAlphabet count) slot input))⟩ :
      TM1.Cfg Bool (BoolLabel count Λ σ) σ) = _
  rw [encode_tape]
  rfl

theorem initial_rows_length (slot : Fin count) (input : List Bool) :
    (TM2to1.trInit (Γ := StackAlphabet count) slot input).length ≤ input.length + 1 := by
  change (input.reverse.map (fun bit => (false,
    Function.update (fun _ : Fin count => (none : Option Bool)) slot (some bit)))).tail.length + 1 ≤ input.length + 1
  rw [List.length_tail, List.length_map, List.length_reverse]
  omega

set_option pp.explicit true in
theorem actual_native_run (machine : Λ → TM2.Stmt (StackAlphabet count) Λ σ)
    (support : Finset Λ) (closed : TM2.Supports machine support)
    (slot : Fin count) (input : List Bool) (finalSource : TM2.Cfg (StackAlphabet count) Λ σ)
    (rest : List (TM2.Cfg (StackAlphabet count) Λ σ))
    (chain : (TM2.init slot input :: rest).IsChain
      (fun before after => TM2.step machine before = some after))
    (last : (TM2.init slot input :: rest).getLast? = some finalSource)
    (halt : finalSource.l = none) (bound actionBound pushBound : Nat)
    (bounded : ∀ state ∈ TM2.init slot input :: rest, ∀ point, (state.stk point).length ≤ bound)
    (counts : ∀ state ∈ TM2.init slot input :: rest, ∀ label, state.l = some label →
      ScannerClock.actions (machine label) ≤ actionBound ∧ AuxWorkspace.pushes (machine label) ≤ pushBound) :
    ∃ (changed : ListBlank (Fin count → Option Bool))
      (trace : List (MachineState (nativeSupport machine support).card))
      (final : MachineState (nativeSupport machine support).card),
      (∀ point, changed.map (proj point) = ListBlank.mk ((finalSource.stk point).map some).reverse) ∧
      Runs (nativeMachine machine support) (FiniteTrackCodec.encodedInput slot input) trace final ∧
      final.Tape = TM1to1.trTape (FiniteTrackCodec.encode_default count)
        (ScannerRun.compiledCfg finalSource changed).Tape ∧
      trace.length ≤ nativeBudget machine support *
        (2 * ((2 * actionBound * (bound + pushBound + 1) + 1) * rest.length)) + 1 ∧
      visitedSpace (nativeMachine machine support) (FiniteTrackCodec.encodedInput slot input).length trace ≤
        FiniteTrackCodec.width count * (bound + pushBound + 6) + 2 * nativeBudget machine support + 1 := by
  obtain ⟨tracks, represented, gammaInitial⟩ := represented_cfg (TM2.init slot input)
    (TM1.init (Γ := FiniteTrackCodec.Track count) (Λ := GammaLabel count Λ σ) (σ := σ)
      (TM2to1.trInit (Γ := StackAlphabet count) slot input))
      (TM2to1.trCfg_init (Γ := StackAlphabet count) (Λ := Λ) (σ := σ) slot input)
  obtain ⟨changed, gammaPosts, changedRep, gammaLength, gammaChain, gammaLast, gammaRange⟩ :=
    LocatedRun.compile_path machine (TM2.init slot input) finalSource rest tracks represented
      chain last bound actionBound pushBound bounded counts
  let gammaStart : LocatedAlphabet.Located (FiniteTrackCodec.Track count) (GammaLabel count Λ σ) σ :=
    LocatedRun.compiledPoint (TM2.init slot input) tracks
  let gammaFinal := LocatedRun.compiledPoint finalSource changed
  have gammaCounts : ∀ state ∈ gammaStart :: gammaPosts, ∀ label, state.1.l = some label →
      AlphabetClock.writes (gammaMachine machine label) + 1 ≤ 2 ∧
        AlphabetPrefix.motionRadius (gammaMachine machine label) ≤ 3 := by
    intro _ _ label _
    exact scanner_bounds machine label
  have gammaCoupled : (gammaStart :: gammaPosts).IsChain (LocatedAlphabet.Step (gammaMachine machine)) := by
    apply gammaChain.imp
    intro before after edge
    rcases before with ⟨⟨active, memory, tape⟩, position⟩
    cases active with
    | none => cases edge.1
    | some label =>
      constructor
      · exact edge.1
      · simpa only [LocatedScanner.net, LocatedAlphabet.net, gammaMachine] using edge.2
  obtain ⟨boolPosts, boolLength, boolChain, boolLast, boolRange⟩ :=
    LocatedAlphabetRun.compile_path FiniteTrackCodec.encode FiniteTrackCodec.decode
      (FiniteTrackCodec.encode_default count) FiniteTrackCodec.decode_encode (gammaMachine machine)
      gammaStart gammaFinal gammaPosts gammaCoupled gammaLast 2 3 0 ((bound + pushBound : Nat) : Int)
      gammaCounts gammaRange
  let boolStart := LocatedAlphabetRun.compiledPoint FiniteTrackCodec.encode
    (FiniteTrackCodec.encode_default count) gammaStart
  let boolFinal := LocatedAlphabetRun.compiledPoint FiniteTrackCodec.encode
    (FiniteTrackCodec.encode_default count) gammaFinal
  have boolInitial : boolStart =
      (TM1.init (Γ := Bool) (Λ := BoolLabel count Λ σ) (σ := σ)
        (FiniteTrackCodec.encodedInput slot input), 0) := by
    change (TM1to1.trCfg FiniteTrackCodec.encode (FiniteTrackCodec.encode_default count)
      (ScannerRun.compiledCfg (TM2.init slot input) tracks), (FiniteTrackCodec.width count : Int) * 0) = _
    rw [gammaInitial, mapped_initial]
    rfl
  have boolFirst : ((boolStart :: boolPosts).map Prod.fst).head? =
      some (TM1.init (FiniteTrackCodec.encodedInput slot input)) := by
    change some boolStart.1 = some (TM1.init _)
    rw [boolInitial]
  have boolCfgChain : ((boolStart :: boolPosts).map Prod.fst).IsChain
      (fun before after => TM1.step (boolMachine machine) before = some after) :=
    List.isChain_map_of_isChain Prod.fst (fun _ _ edge => edge.1) boolChain
  have supportedWeights := SupportClock.trace_weights (boolMachine machine) (boolSupport machine support)
    (bool_supports machine support closed) (FiniteTrackCodec.encodedInput slot input)
      ((boolStart :: boolPosts).map Prod.fst) boolFirst boolCfgChain
  have boolWeights : ∀ state ∈ boolStart :: boolPosts, ∀ label, state.1.l = some label →
      StatementClock.weight (boolMachine machine label) ≤ nativeBudget machine support := by
    intro state present label active
    exact supportedWeights state.1 (List.mem_map.mpr ⟨state, present, rfl⟩) label active
  let lowBool := -(FiniteTrackCodec.width count : Int) * 3
  let highBool := (FiniteTrackCodec.width count : Int) * ((bound + pushBound : Nat) : Int) +
    (FiniteTrackCodec.width count : Int) * 3
  have boolCoordinates : ∀ point ∈ boolStart :: boolPosts, lowBool ≤ point.2 ∧ point.2 ≤ highBool := by
    intro point present
    have within := boolRange point present
    change -(FiniteTrackCodec.width count : Int) * 3 ≤ point.2 ∧
      point.2 ≤ (FiniteTrackCodec.width count : Int) * ((bound + pushBound : Nat) : Int) +
        (FiniteTrackCodec.width count : Int) * 3
    constructor
    · have lower := within.1
      change (FiniteTrackCodec.width count : Int) * 0 - (FiniteTrackCodec.width count : Int) * 3 ≤ point.2 at lower
      simpa only [Int.mul_zero, Int.zero_sub, neg_mul] using lower
    · exact within.2
  obtain ⟨nativePosts, nativeLength, nativeChain, nativeLast, nativeRange⟩ :=
    LocatedNative.compile_path (boolMachine machine) boolStart boolFinal boolPosts boolChain boolLast
      (nativeBudget machine support) lowBool highBool boolWeights boolCoordinates
  let nativeStart := LocatedNative.compiledPoint (boolMachine machine) boolStart
  let nativeFinal := LocatedNative.compiledPoint (boolMachine machine) boolFinal
  have nativeInitial : nativeStart = (TM0.init (FiniteTrackCodec.encodedInput slot input), 0) := by
    change LocatedNative.compiledPoint (boolMachine machine) boolStart = _
    rw [boolInitial]
    rfl
  have nativeHalt : TM0.step (TM1to0.tr (boolMachine machine)) nativeFinal.1 = none := by
    change TM0.step (TM1to0.tr (boolMachine machine))
      (TM1to0.trCfg (boolMachine machine)
        (TM1to1.trCfg FiniteTrackCodec.encode (FiniteTrackCodec.encode_default count)
          (ScannerRun.compiledCfg finalSource changed))) = none
    cases finalSource with
    | mk label store slots =>
      change label = none at halt
      subst label
      rfl
  have nativeTime : nativePosts.length ≤ nativeBudget machine support *
      (2 * ((2 * actionBound * (bound + pushBound + 1) + 1) * rest.length)) :=
    nativeLength.trans (Nat.mul_le_mul_left (nativeBudget machine support)
      (boolLength.trans (Nat.mul_le_mul_left 2 gammaLength)))
  have inputBound : input.length ≤ bound := by
    simpa only [TM2.init, Function.update_self] using bounded (TM2.init slot input) List.mem_cons_self slot
  have inputRowsBound : (FiniteTrackCodec.encodedInput slot input).length ≤
      FiniteTrackCodec.width count * (bound + 1) := by
    rw [FiniteTrackCodec.encoded_length]
    exact Nat.mul_le_mul_left _ ((initial_rows_length slot input).trans (Nat.add_le_add_right inputBound 1))
  have inputNatHigh : (FiniteTrackCodec.encodedInput slot input).length ≤
      FiniteTrackCodec.width count * (bound + pushBound + 3) + nativeBudget machine support := by
    have enlarged := Nat.mul_le_mul_left (FiniteTrackCodec.width count)
      (show bound + 1 ≤ bound + pushBound + 3 by omega)
    omega
  have inputHigh : ((FiniteTrackCodec.encodedInput slot input).length : Int) ≤
      highBool + (nativeBudget machine support : Int) := by
    have highEq : highBool + (nativeBudget machine support : Int) =
        ((FiniteTrackCodec.width count * (bound + pushBound + 3) + nativeBudget machine support : Nat) : Int) := by
      dsimp only [highBool]
      simp only [Int.natCast_add, Int.natCast_mul]
      ring
    rw [highEq]
    omega
  have lowZero : lowBool - (nativeBudget machine support : Int) ≤ 0 := by
    dsimp only [lowBool]
    omega
  have nativeCells := LocatedSpace.source_space_le (boolMachine machine) nativeStart nativeFinal nativePosts
    nativeChain nativeLast nativeHalt (congrArg Prod.snd nativeInitial)
    (FiniteTrackCodec.encodedInput slot input).length
    (lowBool - (nativeBudget machine support : Int)) (highBool + (nativeBudget machine support : Int))
    lowZero inputHigh nativeRange
  have difference : (highBool + (nativeBudget machine support : Int)) -
      (lowBool - (nativeBudget machine support : Int)) =
      ((FiniteTrackCodec.width count * (bound + pushBound + 6) + 2 * nativeBudget machine support : Nat) : Int) := by
    dsimp only [lowBool, highBool]
    simp only [Int.natCast_add, Int.natCast_mul]
    ring
  rw [difference, Int.toNat_natCast] at nativeCells
  have rawFirst : ((nativeStart :: nativePosts).map Prod.fst).head? =
      some (TM0.init (FiniteTrackCodec.encodedInput slot input)) := by
    change some nativeStart.1 = some (TM0.init _)
    rw [nativeInitial]
  have rawChain : ((nativeStart :: nativePosts).map Prod.fst).IsChain
      (fun before after => TM0.step (TM1to0.tr (boolMachine machine)) before = some after) :=
    List.isChain_map_of_isChain Prod.fst (fun _ _ edge => edge.1) nativeChain
  have rawLast : ((nativeStart :: nativePosts).map Prod.fst).getLast? = some nativeFinal.1 := by
    rw [List.getLast?_map, nativeLast, Option.map_some]
  let labels := PSTRSymbolicRelabel.finiteLabels (nativeSupport machine support)
  refine ⟨changed, ((nativeStart :: nativePosts).map Prod.fst).map (PSTRSymbolicRelabel.relabelCfg labels),
    PSTRSymbolicRelabel.relabelCfg labels nativeFinal.1, changedRep,
    PSTRSymbolicRelabel.finite_runs (TM1to0.tr (boolMachine machine)) (nativeSupport machine support)
      (native_supports machine support closed) (FiniteTrackCodec.encodedInput slot input)
      ((nativeStart :: nativePosts).map Prod.fst) nativeFinal.1 rawFirst rawChain rawLast nativeHalt, rfl, ?_, ?_⟩
  · simp only [List.length_map, List.length_cons]
    exact Nat.add_le_add_right nativeTime 1
  · change visitedSpace
      (PSTRSymbolicRelabel.finiteMachine (TM1to0.tr (boolMachine machine)) (nativeSupport machine support))
      (FiniteTrackCodec.encodedInput slot input).length
      (((nativeStart :: nativePosts).map Prod.fst).map
        (PSTRSymbolicRelabel.relabelCfg (PSTRSymbolicRelabel.finiteLabels (nativeSupport machine support)))) ≤ _
    rw [PSTRSymbolicRelabel.finite_visitedSpace (TM1to0.tr (boolMachine machine))
      (nativeSupport machine support) (native_supports machine support closed)
      (FiniteTrackCodec.encodedInput slot input) ((nativeStart :: nativePosts).map Prod.fst) rawFirst rawChain]
    exact nativeCells

end PaperProofs.Common.Native.PSTRWordBool.TM2Native
