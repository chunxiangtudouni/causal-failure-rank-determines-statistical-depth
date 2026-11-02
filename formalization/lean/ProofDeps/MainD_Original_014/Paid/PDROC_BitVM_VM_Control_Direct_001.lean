module

public import Paid.PDROC_BitVM_Kernel_Control_015
public import Paid.PDROC_BitVM_Kernel_CallFamily_022

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.Control

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-- The source ARRAY and its finite PC type are fixed before the raw
input. No Nat address, operand width or input value enters this type. -/
abbrev PC (code : Program) := Fin code.size

/-- Compile-time conversion of a literal address in the fixed source
code. The indirect-jump machine must use actual byte comparisons; it
does not call this definition on the runtime register value. -/
def literalPC (code : Program) (address : Nat) : Option (PC code) :=
  if bound : address < code.size then some ⟨address, bound⟩ else none

def literalEntry {Λ : Type*} (code : Program) (entry : PC code → Λ)
    (failure : Λ) (address : Nat) : Λ :=
  ((literalPC code address).map entry).getD failure

/-- Only fixed source literals are used to construct this statement.
The selected port is reached by a genuine TM2 goto; no stack is changed. -/
def directStatement {Λ σ : Type*} (code : Program) (entry : PC code → Λ)
    (failure : Λ) (address : Nat) : TM2.Stmt Alphabet Λ σ :=
  .goto (fun _ => literalEntry code entry failure address)

def successorStatement {Λ σ : Type*} (code : Program) (entry : PC code → Λ)
    (failure : Λ) (current : PC code) : TM2.Stmt Alphabet Λ σ :=
  directStatement code entry failure (current.val + 1)

theorem literalPC_of_lt (code : Program) (address : Nat) (bound : address < code.size) :
    literalPC code address = some ⟨address, bound⟩ := by
  simp [literalPC, bound]

theorem literalPC_outside (code : Program) (address : Nat) (outside : code.size ≤ address) :
    literalPC code address = none := by
  simp [literalPC, Nat.not_lt.mpr outside]

theorem literalPC_value (code : Program) (address : Nat) (selected : PC code)
    (matched : literalPC code address = some selected) : selected.val = address := by
  unfold literalPC at matched
  split at matched
  · exact (congrArg Fin.val (Option.some.inj matched)).symm
  · cases matched

theorem literalEntry_valid {Λ : Type*} (code : Program) (entry : PC code → Λ)
    (failure : Λ) (address : Nat) (bound : address < code.size) :
    literalEntry code entry failure address = entry ⟨address, bound⟩ := by
  rw [literalEntry, literalPC_of_lt code address bound]
  rfl

theorem literalEntry_invalid {Λ : Type*} (code : Program) (entry : PC code → Λ)
    (failure : Λ) (address : Nat) (outside : code.size ≤ address) :
    literalEntry code entry failure address = failure := by
  rw [literalEntry, literalPC_outside code address outside]
  rfl

theorem direct_stepAux {Λ σ : Type*} (code : Program) (entry : PC code → Λ)
    (failure : Λ) (address : Nat) (store : σ) (contents : Stack → List Bool) :
    TM2.stepAux (directStatement code entry failure address) store contents =
      (⟨some (literalEntry code entry failure address), store, contents⟩ : TM2.Cfg Alphabet Λ σ) := rfl

/-- Caller-relative real edge. The agreement is a fixed code equation,
not a source-run or next-PC eligibility oracle. -/
theorem direct_edge {Λ σ : Type*} (code : Program) (entry : PC code → Λ)
    (failure current : Λ) (address : Nat)
    (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (agrees : machine current = directStatement code entry failure address)
    (store : σ) (contents : Stack → List Bool) :
    TM2.step machine (⟨some current, store, contents⟩ : TM2.Cfg Alphabet Λ σ) =
      some (⟨some (literalEntry code entry failure address), store, contents⟩ : TM2.Cfg Alphabet Λ σ) := by
  change some (TM2.stepAux (machine current) store contents) = _
  rw [agrees, direct_stepAux]

theorem direct_runs {Λ σ : Type*} (code : Program) (entry : PC code → Λ)
    (failure current : Λ) (address : Nat)
    (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (agrees : machine current = directStatement code entry failure address)
    (store : σ) (contents : Stack → List Bool) :
    ∃ run : List (TM2.Cfg Alphabet Λ σ),
      run.head? = some ⟨some current, store, contents⟩ ∧
      run.IsChain (fun before after => TM2.step machine before = some after) ∧
      run.getLast? = some ⟨some (literalEntry code entry failure address), store, contents⟩ ∧
      run.length = 2 := by
  refine ⟨[⟨some current, store, contents⟩, ⟨some (literalEntry code entry failure address), store, contents⟩],
    rfl, List.isChain_cons_cons.mpr ⟨?_, List.isChain_singleton _⟩, rfl, rfl⟩
  exact direct_edge code entry failure current address machine agrees store contents

theorem successor_edge {Λ σ : Type*} (code : Program) (entry : PC code → Λ)
    (failure label : Λ) (current : PC code)
    (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (agrees : machine label = successorStatement code entry failure current)
    (store : σ) (contents : Stack → List Bool) :
    TM2.step machine (⟨some label, store, contents⟩ : TM2.Cfg Alphabet Λ σ) =
      some (⟨some (literalEntry code entry failure (current.val + 1)), store, contents⟩ : TM2.Cfg Alphabet Λ σ) :=
  direct_edge code entry failure label (current.val + 1) machine agrees store contents

/-- An out-of-code literal is sent to a REAL failing halt port. The
successful source-Runs refinement will derive next-fetch validity from
its original trace; this lemma adds no new original qualification. -/
theorem invalid_literal_path {Λ σ : Type*} (code : Program) (entry : PC code → Λ)
    (failure current : Λ) (address : Nat) (outside : code.size ≤ address)
    (machine : Λ → TM2.Stmt Alphabet Λ σ)
    (agrees : machine current = directStatement code entry failure address)
    (fails : machine failure = .halt) (store : σ) (contents : Stack → List Bool) :
    ∃ run : List (TM2.Cfg Alphabet Λ σ),
      run.head? = some ⟨some current, store, contents⟩ ∧
      run.IsChain (fun before after => TM2.step machine before = some after) ∧
      run.getLast? = some ⟨none, store, contents⟩ ∧ run.length = 3 := by
  have first := direct_edge code entry failure current address machine agrees store contents
  rw [literalEntry_invalid code entry failure address outside] at first
  have last : TM2.step machine (⟨some failure, store, contents⟩ : TM2.Cfg Alphabet Λ σ) =
      some ⟨none, store, contents⟩ := by
    change some (TM2.stepAux (machine failure) store contents) = _
    rw [fails]
    rfl
  refine ⟨[⟨some current, store, contents⟩, ⟨some failure, store, contents⟩, ⟨none, store, contents⟩],
    rfl, ?_, rfl, rfl⟩
  exact List.isChain_cons_cons.mpr ⟨first, List.isChain_cons_cons.mpr ⟨last, List.isChain_singleton _⟩⟩

end PDROC.BitVM.VM.Control
