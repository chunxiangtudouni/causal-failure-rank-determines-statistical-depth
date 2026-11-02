module

public import PSTR_WordBool_RatDrop_Resources_006

/-! Exact arbitrary rational result/operand packets, with real disposal.
The original consumer derives owned3 emptiness from its earlier callee. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatDrop

open Turing PSTRWordVM RationalControllerComputation

variable {C : Type*}

def source (result x y : Rat) (tail : List Bool) : List Bool:=
  RatInput.Encoder.packet result (RatInput.Encoder.packet x (RatInput.Encoder.packet y tail))

def budget (background : Stack→List Bool) (result x y : Rat) (tail : List Bool) : Nat:=
  outside background+(source result x y tail).length

def entry (background : Stack→List Bool) (context : C) (memory : RatOutput.Store)
    (result x y : Rat) (tail : List Bool) : State C:=state background 0 context memory (source result x y tail) []

theorem actual_drop (background : Stack→List Bool) (context : C) (memory : RatOutput.Store)
    (result x y : Rat) (tail : List Bool) :
    ∃ trace : List (State C),
      trace.head?=some (entry background context memory result x y tail) ∧
      trace.IsChain (fun a b=>TM2.step (program .halt) a=some b) ∧
      trace.getLast?=some (state background 10 context (false,false) (RatInput.Encoder.packet result tail) []) ∧
      trace.length≤3*RatInput.Encoder.fieldSize result+RatInput.Encoder.fieldSize x+RatInput.Encoder.fieldSize y+17 ∧
      (∀ current∈trace,Safe background context (budget background result x y tail) current ∧
        ∀ slot,(current.stk slot).length≤budget background result x y tail) ∧
      (∀ current∈trace,∀ point,current.l=some point→
        (∀ node∈AuxWorkspace.nodes (program .halt point) current.var current.stk,
          (∀ slot,(node.2 slot).length≤budget background result x y tail+2) ∧
          ∀ slot,slot≠15→slot≠3→node.2 slot=background slot) ∧
        ScannerStatement.clock (program .halt point) current.var current.stk≤8*(budget background result x y tail+3)) ∧
      ∀ current∈trace.dropLast,current.l≠some 10 := by
  obtain ⟨trace,first,chain,last,count,bounds,proper⟩:=actual_drop_fields background context memory
    (PA17TMRatArithmeticParse002.sign result) (PA17TMRatArithmeticParse002.sign x) (PA17TMRatArithmeticParse002.sign y)
    (PA17TMRatArithmeticParse002.numeratorDigits result) (PA17TMRatArithmeticParse002.denominatorDigits result)
    (PA17TMRatArithmeticParse002.numeratorDigits x) (PA17TMRatArithmeticParse002.denominatorDigits x)
    (PA17TMRatArithmeticParse002.numeratorDigits y) (PA17TMRatArithmeticParse002.denominatorDigits y) tail
  refine ⟨trace,first,chain,last,?_,?_,?_,proper⟩
  · dsimp only [RatInput.Encoder.fieldSize]
    omega
  · intro current member
    have safe:=bounds current member
    exact ⟨safe,fun slot=>(RatInput.Encoder.point_mass current.stk slot).trans safe.2.2⟩
  · intro current member point selected
    exact internal_bound background context current _ (bounds current member) point

end PaperProofs.Common.Native.PSTRWordBool.RatDrop
