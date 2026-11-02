module

public import PaperProofs.Paid.PDROC_CalibratedRuntime_001
public import PaperProofs.Common.NativeProtocol

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.CalibratedRuntime

def traceBit (trace : Trace) (offset : ℕ) (truth : Bool) : Option Bool :=
  ((trace)[offset]?).map fun event => if event.1 then !truth else truth

def executionPairs (P : Parameters) (ledger : Ledger P.sharedInstance) : List (ℕ × Fin P.tools) :=
  ledger.executions.map fun execution => (execution.handle.stage.val, (show Fin P.tools from execution.tool))

theorem executionPairs_mem (P : Parameters) (ledger : Ledger P.sharedInstance)
    (stage : P.sharedInstance.Stage) (tool : Fin P.tools) :
    (stage.val, tool) ∈ executionPairs P ledger ↔
      ∃ execution ∈ ledger.executions, execution.handle.stage = stage ∧ execution.tool = tool := by
  constructor
  · intro h
    obtain ⟨execution, he, hpair⟩ := List.mem_map.mp h
    exact ⟨execution, he, Fin.ext (congrArg Prod.fst hpair), congrArg Prod.snd hpair⟩
  · rintro ⟨execution, he, hs, ht⟩
    exact List.mem_map.mpr ⟨execution, he, by simp only [hs, ht]⟩

theorem traceBit_correct_flag (trace : Trace) (offset : ℕ) (truth : Bool) :
    decide (traceBit trace offset truth = some truth) =
      match (trace)[offset]? with | none => false | some event => !event.1 := by
  cases h : (trace)[offset]? with
  | none => simp only [traceBit, h, Option.map_none, reduceCtorEq, decide_false]
  | some event =>
    rcases event with ⟨wrong, repaired⟩
    cases wrong <;> cases truth <;> simp [traceBit, h]

theorem traceBit_wrong_flag (trace : Trace) (offset : ℕ) (truth : Bool) :
    decide (traceBit trace offset truth = some (!truth)) =
      match (trace)[offset]? with | none => false | some event => event.1 := by
  cases h : (trace)[offset]? with
  | none => simp only [traceBit, h, Option.map_none, reduceCtorEq, decide_false]
  | some event =>
    rcases event with ⟨wrong, repaired⟩
    cases wrong <;> cases truth <;> simp [traceBit, h]

theorem decode_wrongBit (bit truth : Bool) :
    (if decide (bit ≠ truth) then !truth else truth) = bit := by
  cases bit <;> cases truth <;> rfl

/-- Strong pure ledger invariant used by both actual backend suffix
inductions. The physical decoder starts from the genuine entry used set. -/
def TraceLedgerMatch (P : Parameters) (cursor : ℕ) (used : Finset (Fin P.tools))
    (trace : Trace) (start ended : State P.sharedInstance) : Prop :=
  (∀ stage : P.sharedInstance.Stage, cursor ≤ stage.val →
    ended.ledger.written stage = traceBit trace (stage.val - cursor) (ended.ledger.truth stage)) ∧
  executionPairs P ended.ledger = executionPairs P start.ledger ++ repairPairs P.tools cursor used trace

theorem traceLedgerMatch_nil (P : Parameters) (cursor : ℕ) (used : Finset (Fin P.tools))
    (start ended : State P.sharedInstance)
    (hw : ∀ stage : P.sharedInstance.Stage, cursor ≤ stage.val → ended.ledger.written stage = none)
    (he : executionPairs P ended.ledger = executionPairs P start.ledger) :
    TraceLedgerMatch P cursor used [] start ended := by
  refine ⟨hw, ?_⟩
  simpa only [repairPairs, List.append_nil] using he

theorem traceLedgerMatch_cons_noRepair (P : Parameters) (cursor : ℕ)
    (used : Finset (Fin P.tools)) (wrong : Bool) (tail : Trace)
    (start middle ended : State P.sharedInstance)
    (hhead : ∀ stage : P.sharedInstance.Stage, stage.val = cursor →
      ended.ledger.written stage = some (if wrong then !(ended.ledger.truth stage) else ended.ledger.truth stage))
    (hmiddle : executionPairs P middle.ledger = executionPairs P start.ledger)
    (hchild : TraceLedgerMatch P (cursor + 1) used tail middle ended) :
    TraceLedgerMatch P cursor used ((wrong, false) :: tail) start ended := by
  refine ⟨?_, ?_⟩
  · intro stage hs
    by_cases hh : stage.val = cursor
    · simpa only [traceBit, hh, Nat.sub_self, List.getElem?_cons_zero, Option.map_some] using hhead stage hh
    · have hoffset : stage.val - cursor = (stage.val - (cursor + 1)) + 1 := by omega
      simp only [traceBit, hoffset, List.getElem?_cons_succ]
      exact hchild.1 stage (by omega)
  · simpa only [repairPairs, Bool.false_eq_true, ite_false, hmiddle] using hchild.2

theorem traceLedgerMatch_cons_repair (P : Parameters) (cursor : ℕ)
    (used : Finset (Fin P.tools)) (tool : Fin P.tools) (tail : Trace)
    (start middle ended : State P.sharedInstance)
    (hhead : ∀ stage : P.sharedInstance.Stage, stage.val = cursor →
      ended.ledger.written stage = some (!(ended.ledger.truth stage)))
    (hfind : unusedTool P.tools used = some tool)
    (hmiddle : executionPairs P middle.ledger = executionPairs P start.ledger ++ [(cursor, tool)])
    (hchild : TraceLedgerMatch P (cursor + 1) (insert tool used) tail middle ended) :
    TraceLedgerMatch P cursor used ((true, true) :: tail) start ended := by
  refine ⟨?_, ?_⟩
  · intro stage hs
    by_cases hh : stage.val = cursor
    · simpa only [traceBit, hh, Nat.sub_self, List.getElem?_cons_zero, Option.map_some, ite_true] using hhead stage hh
    · have hoffset : stage.val - cursor = (stage.val - (cursor + 1)) + 1 := by omega
      simp only [traceBit, hoffset, List.getElem?_cons_succ]
      exact hchild.1 stage (by omega)
  · simpa only [repairPairs, ite_true, hfind, hmiddle, List.append_assoc, List.singleton_append] using hchild.2

end PDROC.CalibratedRuntime
