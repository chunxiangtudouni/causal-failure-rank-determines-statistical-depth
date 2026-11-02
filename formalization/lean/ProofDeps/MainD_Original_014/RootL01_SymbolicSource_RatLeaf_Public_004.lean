module

public import RootL01_SymbolicSource_RatLeaf_Resources_003

/-! Ordinary public actual leaf API and same-path aggregate charge.
All local empty-buffer requirements are explicit.  This is a callee for
the original source, not a new qualification on original symbolicInput. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.RatLeaf

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation

variable {C : Type*}

def support : Finset Label := Finset.univ

theorem supports_stmt (body : Statement C) : TM2.SupportsStmt support body := by
  induction body with
  | push _ _ _ ih | peek _ _ _ ih | pop _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro memory; exact Finset.mem_univ _
  | halt => trivial

theorem supports : TM2.Supports (program (C:=C) .halt) support :=
  ⟨Finset.mem_univ _,fun point _ => supports_stmt (program .halt point)⟩

theorem finiteStore [Finite C] : Finite (Store C) := inferInstance

def statementClock (current : State C) : Nat :=
  match current.l with
  | none => 0
  | some point => ScannerStatement.clock (program .halt point) current.var current.stk

def clockSum (path : List (State C)) : Nat := (path.map statementClock).sum
def chargedCost (path : List (State C)) : Nat := path.length+clockSum path

theorem map_sum_bound {α : Type*} (weight : α → Nat) (path : List α) (bound : Nat)
    (each : ∀ current ∈ path,weight current ≤ bound) :
    (path.map weight).sum ≤ path.length*bound := by
  induction path with
  | nil => simp
  | cons first rest ih =>
    have firstBound := each first List.mem_cons_self
    have restBound := ih (fun current present => each current (List.mem_cons_of_mem _ present))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem costed {background : Bank} {context : C} {memory : RatInput.Store} {formatter : WordNatIO.Store}
    {p : Rat} {tail scratch output : List Bool} {path : List (State C)} {final : State C}
    (facts : Facts background context memory formatter p tail scratch output path final) :
    clockSum path ≤ time p*(30*(scale background context memory formatter p tail scratch output+16)) ∧
    chargedCost path ≤ time p*(30*(scale background context memory formatter p tail scratch output+16)+1) := by
  let bound := 30*(scale background context memory formatter p tail scratch output+16)
  have each : ∀ current ∈ path,statementClock current ≤ bound := by
    intro current present
    cases selected : current.l with
    | none => simp only [statementClock,selected]; exact Nat.zero_le _
    | some point =>
      have limits := internal_resources current point _ (facts.boundaries current present).2.1
      simpa only [statementClock,selected] using limits.2
  have sumBound := (map_sum_bound statementClock path bound each).trans
    (Nat.mul_le_mul_right bound facts.count)
  refine ⟨sumBound,?_⟩
  change path.length+clockSum path ≤ _
  rw [Nat.mul_add,Nat.mul_one]
  exact Nat.add_le_add facts.count sumBound |>.trans_eq (Nat.add_comm _ _)

def initialMass (background : Bank) (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (p : Rat) (tail scratch output : List Bool) : Nat :=
  RatInput.occupied (entry background context memory formatter p tail scratch output).stk

theorem scale_by_actual_mass (background : Bank) (context : C) (memory : RatInput.Store)
    (formatter : WordNatIO.Store) (p : Rat) (tail scratch output : List Bool) :
    time p ≤ 43*(initialMass background context memory formatter p tail scratch output+1) ∧
    scale background context memory formatter p tail scratch output ≤
      1024*(initialMass background context memory formatter p tail scratch output+1) := by
  have mass := RatInput.Encoder.point_mass
    (entry background context memory formatter p tail scratch output).stk (15 : RatInput.Stack)
  change (RatInput.Encoder.packet p tail).length ≤ initialMass background context memory formatter p tail scratch output at mass
  rw [RatInput.Encoder.packet_length] at mass
  dsimp only [time,scale,initialMass] at mass ⊢
  omega

theorem charged_by_actual_mass {background : Bank} {context : C} {memory : RatInput.Store}
    {formatter : WordNatIO.Store} {p : Rat} {tail scratch output : List Bool}
    {path : List (State C)} {final : State C}
    (facts : Facts background context memory formatter p tail scratch output path final) :
    chargedCost path ≤ 4194304*(initialMass background context memory formatter p tail scratch output+1)^2 := by
  have caps := scale_by_actual_mass background context memory formatter p tail scratch output
  have exactCost := (costed facts).2
  let M := initialMass background context memory formatter p tail scratch output+1
  have positive : 1 ≤ M := by dsimp [M]; omega
  have clock : 30*(scale background context memory formatter p tail scratch output+16)+1 ≤ 31201*M := by
    have cap : scale background context memory formatter p tail scratch output ≤ 1024*M := caps.2
    omega
  have product := exactCost.trans (Nat.mul_le_mul caps.1 clock)
  change chargedCost path ≤ 43*M*(31201*M) at product
  change chargedCost path ≤ 4194304*M^2
  nlinarith [Nat.zero_le (M*M)]

namespace Public

theorem actual (background : Bank) (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
    (p : Rat) (tail scratch output : List Bool) :
    ∃ (path : List (State C)) (final : State C),
      Facts background context memory formatter p tail scratch output path final ∧
      chargedCost path ≤ 4194304*(initialMass background context memory formatter p tail scratch output+1)^2 := by
  obtain ⟨path,final,facts⟩ := actual_bounded background context memory formatter p tail scratch output
  exact ⟨path,final,facts,charged_by_actual_mass facts⟩

theorem final_stacks {background : Bank} {context : C} {memory : RatInput.Store} {formatter : WordNatIO.Store}
    {p : Rat} {tail scratch output : List Bool} {path : List (State C)} {final : State C}
    (facts : Facts background context memory formatter p tail scratch output path final) :
    final.stk 13 = (PaperProofs.Common.Native.CompactPrice.encodeExpr (.rational p)).flatMap encodeDatum ++ output ∧
    final.stk 15 = RatInput.Encoder.packet p tail ∧ final.stk 7 = scratch ∧
    final.stk 3 = [] ∧ final.stk 4 = [] ∧ final.stk 5 = [] ∧ final.stk 6 = [] ∧
    final.stk 12 = [] ∧ final.stk 14 = [] := by
  rw [facts.contents]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem fixed_source (C : Type*) [Finite C] :
    ∃ (source : Label → Statement C) (allowed : Finset Label),
      source = program .halt ∧ source .done = .halt ∧ TM2.Supports source allowed ∧
      Finite (Store C) ∧
      ∀ (background : Bank) (context : C) (memory : RatInput.Store) (formatter : WordNatIO.Store)
        (p : Rat) (tail scratch output : List Bool),
        ∃ path final,Facts background context memory formatter p tail scratch output path final ∧
          chargedCost path ≤ 4194304*(initialMass background context memory formatter p tail scratch output+1)^2 := by
  exact ⟨program .halt,support,rfl,rfl,supports,finiteStore,actual⟩

theorem consume_state (before : State C) (p : Rat) (tail scratch : List Bool)
    (active : before.l = some (.collect 0))
    (packet : before.stk 15 = RatInput.Encoder.packet p tail) (old7 : before.stk 7 = scratch)
    (empty3 : before.stk 3 = []) (empty4 : before.stk 4 = [])
    (empty5 : before.stk 5 = []) (empty6 : before.stk 6 = [])
    (empty12 : before.stk 12 = []) (empty14 : before.stk 14 = []) :
    ∃ path final,
      Facts before.stk before.var.1.1 before.var.1.2 before.var.2 p tail scratch (before.stk 13) path final ∧
      path.head? = some before ∧ chargedCost path ≤ 4194304*(RatInput.occupied before.stk+1)^2 := by
  have whole : entry before.stk before.var.1.1 before.var.1.2 before.var.2 p tail scratch (before.stk 13) = before := by
    cases before with
    | mk position memory contents =>
      change position = some (.collect 0) at active
      subst position
      unfold entry
      congr 1
      funext slot
      fin_cases slot <;>
        first
        | rfl
        | exact packet.symm
        | exact old7.symm
        | exact empty3.symm
        | exact empty4.symm
        | exact empty5.symm
        | exact empty6.symm
        | exact empty12.symm
        | exact empty14.symm
  obtain ⟨path,final,facts,cost⟩ := actual before.stk before.var.1.1 before.var.1.2 before.var.2 p tail scratch (before.stk 13)
  refine ⟨path,final,facts,?_,?_⟩
  · exact facts.first.trans (congrArg some whole)
  · simpa only [initialMass,whole] using cost

end Public
end RootL01.SymbolicSource.RatLeaf
