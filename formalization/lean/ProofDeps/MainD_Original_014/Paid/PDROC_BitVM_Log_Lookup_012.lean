module

public import Paid.PDROC_BitVM_Log_Lookup_011
public import Paid.PDROC_BitVM_Log_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Log.Lookup

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! The true lookup macro is related to the exact source live-heap semantics.
This does not implement source instruction dispatch or runtime log encoding.
In particular the pure heap default Nat0 is NOT a successful absent load. -/

def sourceRead (ram : PaperProofs.Paid.Computation.State) (address : ℕ) : Option Cell :=
  if address ∈ ram.live then some (ram.heap address) else none

theorem sourceRead_eq_lookup (events : List HeapEvent) (ram : PaperProofs.Paid.Computation.State)
    (address : ℕ) (refines : Refines events ram) : sourceRead ram address = lookup events address := by
  cases found : lookup events address with
  | none =>
    have absent : address ∉ ram.live := by
      intro member
      have present := (refines.2 address).1 member
      simp only [found, Option.isSome_none, Bool.false_eq_true] at present
    simp only [sourceRead, absent, ↓reduceIte]
  | some value =>
    have present : address ∈ ram.live := (refines.2 address).2 (by simp only [found, Option.isSome_some])
    have heapValue : ram.heap address = value := by
      simpa only [found, Option.getD_some] using refines.1 address
    simp only [sourceRead, present, ↓reduceIte, heapValue]

theorem sourceRead_present (ram : PaperProofs.Paid.Computation.State) (address : ℕ) :
    (sourceRead ram address).isSome = decide (address ∈ ram.live) := by
  by_cases present : address ∈ ram.live <;> simp [sourceRead, present]

/-- This is the official successful/failing RAM load equation. The optional
Cell read by the real Bool lookup has precisely the same failure boundary. -/
theorem execute_load_from_history (input : List Cell) (events : List HeapEvent)
    (ram : PaperProofs.Paid.Computation.State) (target pointer : Register) (address : ℕ)
    (refines : Refines events ram) (pointerValue : ram.register pointer = .natural address) :
    Instruction.execute input (.load target pointer) ram =
      (lookup events address).map (fun value => ({ ram with pc := ram.pc + 1 }).set target value) := by
  rw [← sourceRead_eq_lookup events ram address refines]
  by_cases present : address ∈ ram.live <;>
    simp [Instruction.execute, pointerValue, Cell.nat?, sourceRead, present]

/-- ONE selected real lookup path returns precisely the source read's bytes
and the live predicate. A tombstone therefore reports false/unchanged result. -/
theorem refined_lookup_runs (events : List HeapEvent) (ram : PaperProofs.Paid.Computation.State)
    (address : ℕ) (result : List Bool) (store : Store) (refines : Refines events ram) :
    ∃ (run : List State) (after : State),
      run.head? = some (state (some gateLabel) store (encodeHistory events) [] (encodeNatBits address) result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧
      after.stk = slots (encodeHistory events) [] (encodeNatBits address)
        (valueBytes (sourceRead ram address) ++ result) ∧
      (Query.equality after.var.1 && Query.recordTag after.var.1) = decide (address ∈ ram.live) ∧
      run.length ≤ 100 * (events.length + 1) * ((encodeHistory events).length + 1) := by
  obtain ⟨run, after, head, chain, last, halt, done, data, flag, length⟩ :=
    chronological_lookup_runs events address result store
  refine ⟨run, after, head, chain, last, halt, done, ?_, ?_, length⟩
  · simpa only [sourceRead_eq_lookup events ram address refines] using data
  · rw [← sourceRead_eq_lookup events ram address refines, sourceRead_present] at flag
    exact flag

/-- Source history and its byte bound are derived from the actual source
chain. The genuine lookup path then has polynomial configurations in actual
source time/operand bound; the caller supplies no arbitrary bounded log.
The source-to-log runtime writer/interpreter remains a separate obligation. -/
theorem source_chain_lookup_runs (ramProgram : Array Instruction) (ramInput : List Cell)
    (rest : List PaperProofs.Paid.Computation.State) (budget : ℕ)
    (chain : (initial :: rest).IsChain (fun a b => step ramProgram ramInput a = some b))
    (allBits : ∀ current ∈ initial :: rest, ∀ size ∈ stateCellBits current, size ≤ budget)
    (address : ℕ) (result : List Bool) (store : Store) :
    ∃ (events : List HeapEvent) (run : List State) (after : State),
      Refines events ((initial :: rest).getLast (by simp)) ∧
      run.head? = some (state (some gateLabel) store (encodeHistory events) [] (encodeNatBits address) result) ∧
      run.IsChain (fun a b => TM2.step program a = some b) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      after.l = none ∧
      after.stk = slots (encodeHistory events) [] (encodeNatBits address)
        (valueBytes (sourceRead ((initial :: rest).getLast (by simp)) address) ++ result) ∧
      (Query.equality after.var.1 && Query.recordTag after.var.1) =
        decide (address ∈ ((initial :: rest).getLast (by simp)).live) ∧
      run.length ≤ 100 * (time ramProgram (initial :: rest) + 1) *
        (time ramProgram (initial :: rest) * (4 * budget + 2) + 1) := by
  obtain ⟨events, refines, countSteps, countTime, bytes⟩ :=
    initial_chain_encoded_history ramProgram ramInput rest budget chain allBits
  obtain ⟨run, after, head, actual, last, halt, done, data, flag, length⟩ :=
    refined_lookup_runs events ((initial :: rest).getLast (by simp)) address result store refines
  refine ⟨events, run, after, refines, head, actual, last, halt, done, data, flag, ?_⟩
  exact length.trans (Nat.mul_le_mul
    (Nat.mul_le_mul_left 100 (Nat.add_le_add_right countTime 1))
    (Nat.add_le_add_right bytes 1))

end PDROC.BitVM.Log.Lookup
