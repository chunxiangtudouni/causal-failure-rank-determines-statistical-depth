module

public import Paid.PDMenu_ComputeFrame_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

def joinTrace (first later : List State) : List State := first.dropLast++later

/-- Shared actual endpoint occurs once, so no fictitious state self-step
is inserted when two genuine adjacent execution fragments are joined. -/
theorem joinTrace_chain (program : Program) (input : List Cell) (first later : List State) (middle : State)
    (hfirst : first.IsChain (fun a b => step program input a=some b))
    (hlater : later.IsChain (fun a b => step program input a=some b))
    (hfl : first.getLast?=some middle) (hlh : later.head?=some middle) :
    (joinTrace first later).IsChain (fun a b => step program input a=some b) := by
  have hf : first.dropLast++[middle]=first := List.dropLast_append_getLast? middle (by rw [hfl]; simp)
  cases later with
  | nil => simp at hlh
  | cons head tail =>
      have he : head=middle := Option.some.inj hlh
      subst head
      apply List.isChain_split.mpr
      exact ⟨by rw [hf]; exact hfirst, hlater⟩

theorem joinTrace_time_le (program : Program) (first later : List State) (middle : State)
    (hfl : first.getLast?=some middle) :
    time program (joinTrace first later) ≤ time program first+time program later := by
  have hf : first.dropLast++[middle]=first := List.dropLast_append_getLast? middle (by rw [hfl]; simp)
  have htime : time program first=time program first.dropLast+time program [middle] := by
    calc
      _ = time program (first.dropLast++[middle]) := congrArg (time program) hf.symm
      _ = _ := time_append _ _ _
  change time program (first.dropLast++later) ≤ _
  rw [time_append,htime]
  omega

theorem chain_append_control (program : Program) (input : List Cell) (trace : List State) (before after : State)
    (hc : trace.IsChain (fun a b => step program input a=some b)) (hl : trace.getLast?=some before)
    (hs : step program input before=some after) :
    (trace++[after]).IsChain (fun a b => step program input a=some b) ∧
      time program (trace++[after]) ≤ time program trace+15 := by
  constructor
  · apply hc.append (.singleton after)
    intro x hx y hy
    have hx' : before=x := by simpa only [hl,Option.mem_some_iff] using hx
    have hy' : after=y := by simpa using hy
    subst x
    subst y
    exact hs
  · rw [time_append]
    exact Nat.add_le_add_left (time_singleton_le program after) _

end PDMenu.ComputeFrame
