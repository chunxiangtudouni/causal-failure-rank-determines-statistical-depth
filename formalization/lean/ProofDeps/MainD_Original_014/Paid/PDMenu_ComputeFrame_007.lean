module

public import Paid.PDMenu_ComputeFrame_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

theorem joinTrace_head (first later : List State) (before middle : State)
    (hfh : first.head?=some before) (hfl : first.getLast?=some middle) (hlh : later.head?=some middle) :
    (joinTrace first later).head?=some before := by
  cases first with
  | nil => simp at hfh
  | cons head tail =>
      have he : head=before := Option.some.inj hfh
      subst head
      cases tail with
      | nil =>
          have hm : before=middle := Option.some.inj hfl
          simpa only [joinTrace,List.dropLast_singleton,List.nil_append,hm] using hlh
      | cons next rest => simp only [joinTrace,List.dropLast_cons_cons,List.cons_append,List.head?_cons]

theorem joinTrace_last (first later : List State) (after : State) (hl : later.getLast?=some after) :
    (joinTrace first later).getLast?=some after := by
  have hn : later ≠ [] := by intro he; simp only [he,List.getLast?_nil,reduceCtorEq] at hl
  exact (List.getLast?_append_of_ne_nil first.dropLast hn).trans hl

theorem joinTrace_spec (program : Program) (input : List Cell) (first later : List State)
    (before middle after : State) (firstBound laterBound : ℕ)
    (hfh : first.head?=some before) (hfl : first.getLast?=some middle)
    (hlh : later.head?=some middle) (hll : later.getLast?=some after)
    (hfc : first.IsChain (fun a b => step program input a=some b))
    (hlc : later.IsChain (fun a b => step program input a=some b))
    (hft : time program first ≤ firstBound) (hlt : time program later ≤ laterBound) :
    (joinTrace first later).head?=some before ∧ (joinTrace first later).getLast?=some after ∧
      (joinTrace first later).IsChain (fun a b => step program input a=some b) ∧
      time program (joinTrace first later) ≤ firstBound+laterBound :=
  ⟨joinTrace_head first later before middle hfh hfl hlh,joinTrace_last first later after hll,
    joinTrace_chain program input first later middle hfc hlc hfl hlh,
    (joinTrace_time_le program first later middle hfl).trans (Nat.add_le_add hft hlt)⟩

end PDMenu.ComputeFrame
