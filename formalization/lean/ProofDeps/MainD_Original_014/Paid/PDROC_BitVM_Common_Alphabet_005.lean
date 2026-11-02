module

public import Paid.PDROC_BitVM_Common_TM1_002
public import Common.PSTR_WordBool_AlphabetTrace_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.BitVM.Common

open Turing PaperProofs.Paid.Computation
open PaperProofs.Common.Native.PSTRWordBool

variable {Γ Λ σ : Type*} {n : ℕ}

def alphabetInput (enc : Γ → List.Vector Bool n) (input : List Γ) : List Bool :=
  input.flatMap (fun symbol => (enc symbol).toList)

def alphabetWriteCap (machine : Λ → TM1.Stmt Γ Λ σ) (support : Finset Λ) : ℕ :=
  support.sup (fun label => AlphabetClock.writes (machine label)) + 1

section Encoding

variable [Inhabited Γ]

theorem alphabet_encoded_tape (enc : Γ → List.Vector Bool n)
    (blank : enc default = List.Vector.replicate n false) (input : List Γ) :
    TM1to1.trTape blank (Tape.mk₁ input) = Tape.mk₁ (alphabetInput enc input) := by
  rw [Tape.mk₁, Tape.mk₂, TM1to1.trTape_mk']
  unfold TM1to1.trTape'
  simp only [ListBlank.flatMap_mk, List.flatMap_nil]
  rfl

end Encoding

section Source

variable [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

theorem alphabet_source_supported (machine : Λ → TM1.Stmt Γ Λ σ) (support : Finset Λ)
    (closed : TM1.Supports machine support) (input : List Γ) (trace : List (TM1.Cfg Γ Λ σ))
    (first : trace.head? = some (TM1.init input))
    (chain : trace.IsChain (fun before after => TM1.step machine before = some after)) :
    ∀ state ∈ trace, state.l ∈ Finset.insertNone support := by
  apply chain.induction (fun state => state.l ∈ Finset.insertNone support) trace
  · intro before after edge present
    exact TM1.step_supports machine closed edge present
  · intro nonempty
    have head : trace.head nonempty = TM1.init input :=
      Option.some.inj ((List.head?_eq_some_head nonempty).symm.trans first)
    rw [head]
    exact Finset.some_mem_insertNone.mpr closed.1

/-- The genuine alphabet compiler path. Every executed source label's
write allowance is derived from its real closed support, not supplied as
a numerical run oracle. Original physical input here is the explicit fixed
alphabet encoding, not a free adapter from another Bool stream. -/
theorem alphabet_actual_tm1_trace (enc : Γ → List.Vector Bool n)
    (dec : List.Vector Bool n → Γ) (blank : enc default = List.Vector.replicate n false)
    (inverse : ∀ symbol, dec (enc symbol) = symbol)
    (machine : Λ → TM1.Stmt Γ Λ σ) (support : Finset Λ) (closed : TM1.Supports machine support)
    (input : List Γ) (sourceTrace : List (TM1.Cfg Γ Λ σ)) (sourceFinal : TM1.Cfg Γ Λ σ)
    (first : sourceTrace.head? = some (TM1.init input))
    (chain : sourceTrace.IsChain (fun before after => TM1.step machine before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) (halt : TM1.step machine sourceFinal = none) :
    ∃ (trace : List (TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ)) (final : TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ),
      trace.head? = some (TM1.init (alphabetInput enc input)) ∧
      trace.IsChain (fun before after => TM1.step (TM1to1.tr enc dec machine) before = some after) ∧
      trace.getLast? = some final ∧ TM1.step (TM1to1.tr enc dec machine) final = none ∧
      final.Tape = TM1to1.trTape blank sourceFinal.Tape ∧
      trace.length ≤ alphabetWriteCap machine support * sourceTrace.length + 1 := by
  have supported := alphabet_source_supported machine support closed input sourceTrace first chain
  cases sourceTrace with
  | nil => simp at first
  | cons start rest =>
    have initial : start = TM1.init input := Option.some.inj first
    subst start
    have weights : ∀ state ∈ TM1.init input :: rest, ∀ label, state.l = some label →
        AlphabetClock.writes (machine label) + 1 ≤ alphabetWriteCap machine support := by
      intro state member label active
      have inside := supported state member
      rw [active] at inside
      exact Nat.add_le_add_right (Finset.le_sup (f := fun q => AlphabetClock.writes (machine q))
        (Finset.some_mem_insertNone.mp inside)) 1
    obtain ⟨posts, length, actualChain, actualLast⟩ :=
      AlphabetTrace.compile_path enc dec blank inverse machine (alphabetWriteCap machine support)
        (TM1.init input) sourceFinal rest chain last weights
    have mappedInitial : TM1to1.trCfg enc blank (TM1.init (Γ := Γ) (Λ := Λ) (σ := σ) input) =
        TM1.init (Γ := Bool) (Λ := TM1to1.Λ' Γ Λ σ) (σ := σ) (alphabetInput enc input) := by
      change (⟨some (.normal default), default, TM1to1.trTape blank (Tape.mk₁ input)⟩ :
        TM1.Cfg Bool (TM1to1.Λ' Γ Λ σ) σ) = _
      rw [alphabet_encoded_tape enc blank input]
      rfl
    refine ⟨TM1to1.trCfg enc blank (TM1.init input) :: posts, TM1to1.trCfg enc blank sourceFinal,
      congrArg some mappedInitial, actualChain, actualLast, ?_, ?_, ?_⟩
    · cases sourceFinal with
      | mk label store tape =>
        cases label with
        | none => rfl
        | some label => cases halt
    · cases sourceFinal
      rfl
    · change posts.length + 1 ≤ alphabetWriteCap machine support * (rest.length + 1) + 1
      exact Nat.add_le_add_right (length.trans (Nat.mul_le_mul_left _ (by omega))) 1

end Source

section Finite

variable [Inhabited Γ] [Fintype Γ] [Inhabited Λ] [Inhabited σ] [Fintype σ]

/-- Γ, code width, encoder/decoder, σ and closed code support are all
fixed before input. In particular no runtime word width becomes Γ or σ. -/
noncomputable def alphabetBitMachine (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
    (machine : Λ → TM1.Stmt Γ Λ σ) (support : Finset Λ) :
    BitMachine (tm1NativeSupport (TM1to1.tr enc dec machine) (TM1to1.trSupp machine support)).card :=
  tm1BitMachine (TM1to1.tr enc dec machine) (TM1to1.trSupp machine support)

noncomputable def alphabetBitBudget (enc : Γ → List.Vector Bool n) (dec : List.Vector Bool n → Γ)
    (machine : Λ → TM1.Stmt Γ Λ σ) (support : Finset Λ) (sourceLength : ℕ) : ℕ :=
  SupportClock.clock (TM1to1.tr enc dec machine) (TM1to1.trSupp machine support) *
    (alphabetWriteCap machine support * sourceLength + 1) + 1

/-- Same selected compiled witness, full encoded Tape, real HALT and
original BitRuns/time/visited space. This conditional finite compiler does
not supply original raw6 parsing or final naked artifact output adapters. -/
theorem alphabet_actual_bit_trace (enc : Γ → List.Vector Bool n)
    (dec : List.Vector Bool n → Γ) (blank : enc default = List.Vector.replicate n false)
    (inverse : ∀ symbol, dec (enc symbol) = symbol)
    (machine : Λ → TM1.Stmt Γ Λ σ) (support : Finset Λ) (closed : TM1.Supports machine support)
    (input : List Γ) (sourceTrace : List (TM1.Cfg Γ Λ σ)) (sourceFinal : TM1.Cfg Γ Λ σ)
    (first : sourceTrace.head? = some (TM1.init input))
    (chain : sourceTrace.IsChain (fun before after => TM1.step machine before = some after))
    (last : sourceTrace.getLast? = some sourceFinal) (halt : TM1.step machine sourceFinal = none) :
    ∃ trace final,
      BitRuns (alphabetBitMachine enc dec machine support) (alphabetInput enc input) trace final ∧
      final.Tape = TM1to1.trTape blank sourceFinal.Tape ∧
      trace.length ≤ alphabetBitBudget enc dec machine support sourceTrace.length ∧
      visitedBitSpace (alphabetBitMachine enc dec machine support) (alphabetInput enc input).length trace ≤
        (alphabetInput enc input).length + 2 * alphabetBitBudget enc dec machine support sourceTrace.length + 1 := by
  obtain ⟨boolTrace, boolFinal, boolFirst, boolChain, boolLast, boolHalt, boolTape, boolBound⟩ :=
    alphabet_actual_tm1_trace enc dec blank inverse machine support closed input sourceTrace sourceFinal first chain last halt
  have closedBool := TM1to1.tr_supports enc dec machine closed
  obtain ⟨trace, final, actual, tape, length, _space⟩ :=
    tm1_actual_bit_trace (TM1to1.tr enc dec machine) (TM1to1.trSupp machine support) closedBool
      (alphabetInput enc input) boolTrace boolFinal boolFirst boolChain boolLast boolHalt
  have bounded : trace.length ≤ alphabetBitBudget enc dec machine support sourceTrace.length :=
    length.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ boolBound) 1)
  exact ⟨trace, final, actual, tape.trans boolTape, bounded,
    visitedBitSpace_of_clock _ _ _ _ bounded⟩

end Finite

end PDROC.BitVM.Common
