module
public import B23_6_DFSFrame_Resources011

/-! Caller splicing preserves the very same physical trace, store and scanner
clock. All three caller ports are active endpoints, never callee steps. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C Ω : Type*}

theorem clock_labelMap (mapping : Label → Ω) (body : Statement C) (memory : Store C) (before : Bank) :
    ScannerStatement.clock (LabelMap.statement mapping body) memory before=ScannerStatement.clock body memory before := by
  induction body generalizing memory before with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih => simp only [LabelMap.statement,ScannerStatement.clock,ih]
  | load value _ ih => exact ih (value memory) before
  | branch test _ _ yes no =>
    cases choice : test memory <;>
      simp only [LabelMap.statement,ScannerStatement.clock,choice,Bool.false_eq_true,ite_false,ite_true,yes,no]
  | goto _ | halt => rfl

def callerClock (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (current : TM2.Cfg RatInput.Alphabet Ω (Store C)) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (code point) current.var current.stk
def callerClockSum (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (path : List (TM2.Cfg RatInput.Alphabet Ω (Store C))) : Nat := (path.dropLast.map (callerClock code)).sum

theorem caller_chain {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)}
    (facts : Facts entry exit memory before output path) (mapping : Label → Ω)
    (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (agrees : ∀ point,Interior point→code (mapping point)=LabelMap.statement mapping (source point)) :
    (path.map (LabelMap.configuration mapping)).IsChain (fun a b => TM2.step code a=some b) := by
  apply LabelMap.chain_configuration_on mapping source code path facts.chain
  intro current member point selected
  obtain ⟨actual,active,proper⟩:=(facts.proper current member).1
  have equal : point=actual:=Option.some.inj (selected.symm.trans active)
  subst point
  exact agrees actual proper

theorem caller_clock_sum {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)}
    (facts : Facts entry exit memory before output path) (mapping : Label → Ω)
    (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (agrees : ∀ point,Interior point→code (mapping point)=LabelMap.statement mapping (source point)) :
    callerClockSum code (path.map (LabelMap.configuration mapping))=clockSum path := by
  unfold callerClockSum clockSum
  rw [←List.map_dropLast,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro current member
  obtain ⟨point,active,proper⟩:=(facts.proper current member).1
  change (match current.l.map mapping with
    | none => 0
    | some point => ScannerStatement.clock (code point) current.var current.stk)=statementClock current
  simp only [statementClock,active,Option.map_some]
  rw [agrees point proper,clock_labelMap]

theorem caller_internal {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)}
    (facts : Facts entry exit memory before output path) (mapping : Label → Ω)
    (code : Ω → TM2.Stmt RatInput.Alphabet Ω (Store C))
    (agrees : ∀ point,Interior point→code (mapping point)=LabelMap.statement mapping (source point)) :
    ∀ current∈path.dropLast,∀ point,current.l=some point→
      (∀ node∈AuxWorkspace.nodes (code (mapping point)) current.var current.stk,node.1.1=memory.1 ∧
        (∀ slot,(node.2 slot).length≤160*scale before) ∧ RatInput.occupied node.2≤2560*scale before) ∧
      ScannerStatement.clock (code (mapping point)) current.var current.stk≤1280*scale before := by
  intro current member point selected
  obtain ⟨actual,active,proper⟩:=(facts.proper current member).1
  have equal : point=actual:=Option.some.inj (selected.symm.trans active)
  subst point
  rw [agrees actual proper,LabelMap.nodes_statement,clock_labelMap]
  exact (facts.proper current member).2 actual active

theorem caller_noearly {entry exit : Label} {memory : Store C} {before output : Bank} {path : List (State C)}
    (facts : Facts entry exit memory before output path) (mapping : Label ↪ Ω) :
    ∀ current∈(path.map (LabelMap.configuration mapping)).dropLast,
      current.l≠some (mapping .pushDone) ∧ current.l≠some (mapping (.popDone true)) ∧ current.l≠some (mapping (.popDone false)) := by
  intro current member
  rw [←List.map_dropLast] at member
  obtain ⟨original,present,rfl⟩:=List.mem_map.mp member
  obtain ⟨point,active,proper⟩:=(facts.proper original present).1
  change original.l.map mapping≠_ ∧ original.l.map mapping≠_ ∧ original.l.map mapping≠_
  rw [active,Option.map_some]
  refine ⟨?_,?_,?_⟩
  · intro equal;exact proper.1 (mapping.injective (Option.some.inj equal))
  · intro equal;exact proper.2.1 (mapping.injective (Option.some.inj equal))
  · intro equal;exact proper.2.2 (mapping.injective (Option.some.inj equal))

theorem caller_support (mapping : Label → Ω) (allowed : Finset Ω)
    (maps : ∀ point,mapping point∈allowed) (point : Label) :
    TM2.SupportsStmt allowed (LabelMap.statement mapping (source (C:=C) point)) := by
  apply LabelMap.statement_supports mapping (source point) Finset.univ allowed
  · exact (supports (.halt : Statement C) .halt .halt).2 point (Finset.mem_univ _)
  · intro point _;exact maps point

end B23_6.DFSFrame
