module

public import PaperProofs.Structure.RawIncidenceLaminarFullRAM
public import PaperProofs.Structure.RawIncidenceScanSafety
import Mathlib.Tactic.IntervalCases

/-! Finite-prefix bounds for the original fixed raw-incidence checker.
The arithmetic and access lemmas below execute the existing instructions;
they introduce neither a checker result nor a new machine instruction. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

section BasicBounds

attribute [local simp] runOps natExecuteOp Op.execute Instruction.execute
  testCell loadCell incrementCell storeCell jumpTo RegistersBound registerBound

set_option maxRecDepth 10000 in
theorem testCell_prefix_registerBound (N q : Nat) (rom : PhysicalROM)
    (bound counter exit : Nat) (state : NatState) (hr : RegistersBound N q state)
    (hb : bound < 8) (hc : counter < 8) (he : exit ≤ 126)
    (hv : state.heap bound ≤ registerBound N q) (hw : state.heap counter ≤ registerBound N q)
    (count : Nat) (hcount : count ≤ 7) :
    RegistersBound N q (runOps rom ((testCell bound counter exit).take count) state) := by
  have ha := hr .address
  have hi := hr .index
  have hval := hr .value
  have ht := hr .total
  have ho := hr .old
  have hf := hr .fresh
  have hflag := hr .flag
  intro reg
  cases reg <;> interval_cases count <;> simp_all +decide <;> omega

set_option maxRecDepth 10000 in
theorem incrementCell_prefix_registerBound (N q : Nat) (rom : PhysicalROM)
    (cell : Nat) (state : NatState) (hr : RegistersBound N q state) (hc : cell < 8)
    (hv : state.heap cell + 1 ≤ registerBound N q) (count : Nat) (hcount : count ≤ 6) :
    RegistersBound N q (runOps rom ((incrementCell cell).take count) state) := by
  have ha := hr .address
  have hi := hr .index
  have hval := hr .value
  have ht := hr .total
  have ho := hr .old
  have hf := hr .fresh
  have hflag := hr .flag
  intro reg
  cases reg <;> interval_cases count <;> simp_all +decide <;> omega

set_option maxRecDepth 10000 in
theorem jumpTo_prefix_registerBound (N q : Nat) (rom : PhysicalROM)
    (exit : Nat) (state : NatState) (hr : RegistersBound N q state) (he : exit ≤ 126)
    (count : Nat) (hcount : count ≤ 3) :
    RegistersBound N q (runOps rom ((jumpTo exit).take count) state) := by
  have ha := hr .address
  have hi := hr .index
  have hval := hr .value
  have ht := hr .total
  have ho := hr .old
  have hf := hr .fresh
  have hflag := hr .flag
  intro reg
  cases reg <;> interval_cases count <;> simp_all +decide <;> omega

theorem testCell_prefix_accessFits (rom : PhysicalROM) (bound counter exit : Nat)
    (state : NatState) (hb : bound < 8) (hc : counter < 8)
    (count : Nat) (hcount : count < (testCell bound counter exit).length) :
    NatAccessFits rom 8 (runOps rom ((testCell bound counter exit).take count) state)
      (testCell bound counter exit)[count] := by
  have hn : count ≤ 6 := by change count < 7 at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp_all +decide [NatAccessFits, AccessFits]

theorem incrementCell_prefix_accessFits (rom : PhysicalROM) (cell : Nat)
    (state : NatState) (hc : cell < 8)
    (count : Nat) (hcount : count < (incrementCell cell).length) :
    NatAccessFits rom 8 (runOps rom ((incrementCell cell).take count) state)
      (incrementCell cell)[count] := by
  have hn : count ≤ 5 := by change count < 6 at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp_all +decide [NatAccessFits, AccessFits]

theorem jumpTo_prefix_accessFits (rom : PhysicalROM) (exit : Nat) (state : NatState)
    (count : Nat) (hcount : count < (jumpTo exit).length) :
    NatAccessFits rom 8 (runOps rom ((jumpTo exit).take count) state) (jumpTo exit)[count] := by
  have hn : count ≤ 2 := by change count < 3 at hcount; omega
  interval_cases count <;> exact True.intro

end BasicBounds

end PaperProofs.Structure.LaminarTree.RawIncidenceMacroSafety
