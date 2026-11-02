module

public import PaperProofs.Paid.MenuCompiler
public import Mathlib.Data.List.FinRange

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Positive genuine unused cardinality prevents the literal find? routine
from introducing a fallback abandonment. -/
theorem menuUnusedTool_exists_of_available (P : Parameters) (N K : ℕ)
    (history : List (VisibleEvent (freshInstance N K)))
    (hpos : 0 < (Finset.univ \ historyUsed history).card) :
    ∃ tool, P.menuUnusedTool N K history = some tool := by
  classical
  obtain ⟨tool, htool⟩ := Finset.card_pos.mp hpos
  have hu : tool ∉ historyUsed history := (Finset.mem_sdiff.mp htool).2
  cases hf : P.menuUnusedTool N K history with
  | some selected => exact ⟨selected, rfl⟩
  | none =>
    have hn := List.find?_eq_none.mp hf tool (List.mem_finRange tool)
    exact (hn (decide_eq_true hu)).elim

/-- With r original tools already used in ascending order, the actual
finite-list query returns exactly tool r, whenever it returns a tool. -/
theorem menuUnusedTool_val_of_initial_segment (P : Parameters) (N K r : ℕ)
    (history : List (VisibleEvent (freshInstance N K)))
    (hused : ∀ tool : (freshInstance N K).Tool, tool ∈ historyUsed history ↔ tool.val < r)
    (tool : (freshInstance N K).Tool) (hfind : P.menuUnusedTool N K history = some tool) :
    tool.val = r := by
  classical
  have hfind' : (List.finRange K).find? (fun selected => selected ∉ historyUsed history) = some tool := hfind
  obtain ⟨hunused, index, hindex, hget, hbefore⟩ := List.find?_eq_some_iff_getElem.mp hfind'
  have hindexValue : ((List.finRange K)[index]'hindex).val = index :=
    congrArg Fin.val (List.getElem_finRange hindex)
  have hi : index = tool.val := hindexValue.symm.trans (congrArg Fin.val hget)
  have hu : tool ∉ historyUsed history := of_decide_eq_true hunused
  have hrle : r ≤ tool.val := Nat.le_of_not_gt (fun hlt => hu ((hused tool).mpr hlt))
  apply le_antisymm _ hrle
  by_contra hnot
  have hlt : r < tool.val := lt_of_not_ge hnot
  have hri : r < index := hlt.trans_eq hi.symm
  have hrlen : r < (List.finRange K).length := hri.trans hindex
  let candidate : (freshInstance N K).Tool := (List.finRange K)[r]'hrlen
  have hvalue : candidate.val = r := congrArg Fin.val (List.getElem_finRange hrlen)
  have hru : candidate ∉ historyUsed history := by
    intro hc
    have hlt' := (hused candidate).mp hc
    rw [hvalue] at hlt'
    exact Nat.lt_irrefl r hlt'
  have hflag : decide (candidate ∉ historyUsed history) = true := decide_eq_true hru
  have hbad : !decide (candidate ∉ historyUsed history) = true := hbefore r hri
  have hfalse : (false : Bool) = true := (congrArg Bool.not hflag).symm.trans hbad
  cases hfalse

end PDMenu
