module

public import RootB234_PrepBudgetArchive_Resources003
public import Common.PSTR_SYM_LaneArchive_044

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepBudgetArchive
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open scoped BigOperators
variable {C : Type*}

theorem reversed_falsePairs (digits : List Bool) :
    (PSTRSymbolicLaneScan.navigationCells (PSTRSymbolicLaneArchive.falsePairs digits)).reverse=
      backCells digits.reverse := by
  induction digits with
  | nil => rfl
  | cons digit later ih =>
      change (false::digit::PSTRSymbolicLaneScan.navigationCells
        (PSTRSymbolicLaneArchive.falsePairs later)).reverse=backCells (digit::later).reverse
      rw [List.reverse_cons,List.reverse_cons,ih]
      simp [backCells,List.reverse_cons,List.flatMap_append,List.append_assoc]

theorem paired_prefix (later : List Bool) (first near : Bool) (older : List Bool)
    (negative boundary : Bool) (left : List Bool) :
    (PSTRSymbolicLaneScan.navigationCells (PSTRSymbolicLaneArchive.rationalPairs negative
      (near::older).reverse first later.reverse)).reverse ++ boundary::true::left =
      true::true::denSource later first near negative boundary older left := by
  simp only [PSTRSymbolicLaneArchive.rationalPairs,PSTRSymbolicLaneArchive.navigationCells_append,
    List.reverse_append,reversed_falsePairs,List.reverse_reverse]
  simp [PSTRSymbolicLaneScan.navigationCells,denSource,List.append_assoc]

theorem packet_exact (negative : Bool) (numerator denominator target : List Bool) :
    true::negative::(frontCells numerator ++ false::false::(frontCells denominator ++ false::false::target)) =
      PSTRSymbolicRatExport.packet negative numerator denominator target := rfl

def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program .halt point) current.var current.stk

def traceClockSum (trace : List (State C)) : Nat := (trace.dropLast.map statementClock).sum

theorem trace_boundary (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool)
    (current : State C)
    (member : current∈actualTrace background context bit flag pending later first near older negative boundary left target) :
    current.var.1=context ∧
      (∀ point,¬Work point → current.stk point=background point) ∧
      ∀ point,(current.stk point).length ≤ initialMass background later first near older negative boundary left target+2 := by
  have within := actual_bound background context bit flag pending later first near older negative boundary left target current member
  refine ⟨?_,?_,work_actual_stack background context later first near older negative boundary left target current within⟩
  · obtain ⟨p,b,f,d,s,t,rfl,_⟩ := within
    rfl
  · intro point untouched
    obtain ⟨p,b,f,d,s,t,rfl,_⟩ := within
    simp only [Work,not_or] at untouched
    simp only [state,bank,untouched.1,untouched.2,ite_false]

theorem trace_internal (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool)
    (current : State C)
    (member : current∈actualTrace background context bit flag pending later first near older negative boundary left target)
    (label : Label) (node : AuxWorkspace.Snapshot (Γ:=Alphabet) (σ:=Store C))
    (inside : node∈AuxWorkspace.nodes (program .halt label) current.var current.stk) :
    node.1.1=context ∧ (∀ point,¬Work point → node.2 point=background point) ∧
      (∀ point,(node.2 point).length≤scale background later first near older negative boundary left target) ∧
      ScannerStatement.clock (program .halt label) current.var current.stk≤
        12*scale background later first near older negative boundary left target := by
  have bounds := trace_boundary background context bit flag pending later first near older negative boundary left target current member
  refine ⟨(nodes_context label current.var current.stk node inside).trans bounds.1,?_,?_,?_⟩
  · intro point untouched
    exact (nodes_frame label current.var current.stk point untouched node inside).trans (bounds.2.1 point untouched)
  · intro point
    have raw := AuxWorkspace.node_bound (program .halt label) current.var current.stk
      (initialMass background later first near older negative boundary left target+2) bounds.2.2 node inside point
    have pushes := fixed_pushes (C:=C) label
    simp only [scale]
    omega
  · have raw := ScannerClock.clock_bound (program .halt label) current.var current.stk
      (initialMass background later first near older negative boundary left target+2) bounds.2.2
    have actions := fixed_actions (C:=C) label
    have pushes := fixed_pushes (C:=C) label
    exact raw.trans (Nat.mul_le_mul (by omega) (by simp only [scale]; omega))

theorem trace_clock (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool)
    (current : State C)
    (member : current∈actualTrace background context bit flag pending later first near older negative boundary left target) :
    statementClock current≤12*scale background later first near older negative boundary left target := by
  have bound := (trace_boundary background context bit flag pending later first near older negative boundary left target current member).2.2
  cases selected : current.l with
  | none => simp [statementClock,selected]
  | some point =>
      simp only [statementClock,selected]
      have raw := ScannerClock.clock_bound (program .halt point) current.var current.stk
        (initialMass background later first near older negative boundary left target+2) bound
      exact raw.trans (Nat.mul_le_mul (by have := fixed_actions (C:=C) point; omega)
        (by have := fixed_pushes (C:=C) point; simp only [scale]; omega))

theorem actual_time (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    (actualTrace background context bit flag pending later first near older negative boundary left target).length≤
      scale background later first near older negative boundary left target := by
  have bound := inputs_le_mass background later first near older negative boundary left target
  simp only [actualTrace,List.length_cons,den_length,scale]
  omega

theorem actual_clock_sum (background : Stack → List Bool) (context : C) (bit flag pending : Bool)
    (later : List Bool) (first near : Bool) (older : List Bool) (negative boundary : Bool) (left target : List Bool) :
    traceClockSum (actualTrace background context bit flag pending later first near older negative boundary left target)≤
      12*(scale background later first near older negative boundary left target)^2 := by
  let run := actualTrace background context bit flag pending later first near older negative boundary left target
  let S := scale background later first near older negative boundary left target
  have terms : ∀ n∈run.dropLast.map statementClock,n≤12*S := by
    intro n member
    obtain ⟨current,present,rfl⟩ := List.mem_map.mp member
    exact trace_clock background context bit flag pending later first near older negative boundary left target
      current (List.dropLast_subset run present)
  have total : traceClockSum run≤run.dropLast.length*(12*S) := by
    simpa only [traceClockSum,List.length_map,Nat.nsmul_eq_mul] using
      List.sum_le_length_nsmul (run.dropLast.map statementClock) (12*S) terms
  have count : run.dropLast.length≤S := by
    rw [List.length_dropLast]
    exact (Nat.sub_le run.length 1).trans (actual_time background context bit flag pending later first near older negative boundary left target)
  exact total.trans ((Nat.mul_le_mul_right _ count).trans_eq (by ring))

namespace Public

theorem actual_paired (caller : Statement C) (background : Stack → List Bool) (context : C)
    (bit flag pending : Bool) (later : List Bool) (first near : Bool) (older : List Bool)
    (negative boundary : Bool) (left target : List Bool) :
    ∃ run : List (State C),
      run.head?=some (state background 0 context bit flag pending
        ((PSTRSymbolicLaneScan.navigationCells (PSTRSymbolicLaneArchive.rationalPairs negative
          (near::older).reverse first later.reverse)).reverse ++ boundary::true::left) target) ∧
      run.IsChain (fun before after => TM2.step (program caller) before=some after) ∧
      run.getLast?=some (state background 4 context boundary true negative (boundary::true::left)
        (PSTRSymbolicRatExport.packet negative (near::older).reverse (first::later.reverse) target)) ∧
      run=actualTrace background context bit flag pending later first near older negative boundary left target ∧
      run.length≤scale background later first near older negative boundary left target ∧
      traceClockSum run≤12*(scale background later first near older negative boundary left target)^2 := by
  let run := actualTrace background context bit flag pending later first near older negative boundary left target
  refine ⟨run,?_,?_,?_,rfl,actual_time _ _ _ _ _ _ _ _ _ _ _ _ _,actual_clock_sum _ _ _ _ _ _ _ _ _ _ _ _ _⟩
  · rw [paired_prefix]
    rfl
  · apply List.isChain_cons.mpr
    refine ⟨?_,den_chain caller _ _ _ _ _ _ _ _ _ _ _ _ _⟩
    intro next head
    rw [den_head] at head
    have same := (Option.mem_some_iff.mp head).symm
    subst next
    exact step_entry caller background context bit flag pending _ _
  · change (actualTrace background context bit flag pending later first near older negative boundary left target).getLast?=_
    rw [actualTrace,List.getLast?_cons_of_ne_nil (den_nonempty _ _ _ _ _ _ _ _ _ _ _ _ _),den_last]
    rfl

theorem fixed_source (C : Type*) [Fintype C] :
    ∃ (source : Label → Statement C) (support : Finset Label),
      source=program .halt ∧ support.card=5 ∧ TM2.Supports source support :=
  ⟨program .halt,Finset.univ,rfl,by decide,supports .halt⟩

end Public
end RootB234.PrepBudgetArchive
