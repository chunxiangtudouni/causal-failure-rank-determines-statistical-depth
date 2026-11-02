module
public import RootB236_Controller_DFSDriver_NodeEntry006
public import B23_6_DFSFrame_Public013

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
abbrev Core := RootB236.Controller.DFSDriver.Label
abbrev Label := Sum Core B23_6.DFSFrame.Label
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)
variable {C : Type*}
def coreMap (point : Core) : Label :=
  if point=pushGood then .inr (.pushBoot true) else if point=pushBad then .inr (.pushBoot false) else
    if point=popFrame then .inr .popBoot else .inl point
def frameMap : B23_6.DFSFrame.Label → Label
  | .pushDone => .inl entry
  | .popDone true => .inl returnedGood
  | .popDone false => .inl returnedBad
  | point => .inr point

def program (finish : Statement C) : Label → Statement C
  | .inl point => if point=rootDone then finish else LabelMap.statement coreMap (source point)
  | .inr point => LabelMap.statement frameMap (StoreIso.statement BestUpdate.storeIso (B23_6.DFSFrame.source (C:=C×Ordering) point))
def done : Label := .inl rootDone
def start : Label := .inl entry

theorem core_code (finish : Statement C) (point : Core) (proper : ¬Boundary point) :
    program finish (coreMap point)=LabelMap.statement coreMap (source point) := by
  have ng : point≠pushGood := by intro same;subst point;exact proper (Or.inl rfl)
  have nb : point≠pushBad := by intro same;subst point;exact proper (Or.inr (Or.inl rfl))
  have np : point≠popFrame := by intro same;subst point;exact proper (Or.inr (Or.inr (Or.inl rfl)))
  have nd : point≠rootDone := by intro same;subst point;exact proper (Or.inr (Or.inr (Or.inr rfl)))
  simp only [coreMap,ng,nb,np,nd,ite_false,program]
theorem frame_code (finish : Statement C) (point : B23_6.DFSFrame.Label) (proper : B23_6.DFSFrame.Interior point) :
    program finish (frameMap point)=LabelMap.statement frameMap
      (StoreIso.statement BestUpdate.storeIso (B23_6.DFSFrame.source (C:=C×Ordering) point)) := by
  cases point
  all_goals try rfl
  · exact False.elim (proper.1 rfl)
  · rename_i kind;cases kind
    · exact False.elim (proper.2.2 rfl)
    · exact False.elim (proper.2.1 rfl)

private theorem closed (body : Statement C) : TM2.SupportsStmt (Finset.univ : Finset Label) body := by
  induction body with
  | push _ _ _ ih | pop _ _ _ ih | peek _ _ _ ih | load _ _ ih => exact ih
  | branch _ _ _ yes no => exact ⟨yes,no⟩
  | goto target => intro memory;exact Finset.mem_univ (target memory)
  | halt => trivial
theorem supports (finish : Statement C) : TM2.Supports (program finish) (Finset.univ : Finset Label) :=
  ⟨Finset.mem_univ _,fun point _ => closed (program finish point)⟩
theorem finite_store [Finite C] : Finite (Store C) := inferInstance

/-- Every edge below belongs to the one fully instantiated core+frame source. -/
inductive Run (finish : Statement C) : State C → State C → Nat → Prop where
  | refl {current} : Run finish current current 0
  | step {before after final steps} (proper : before.l≠some done)
      (edge : TM2.step (program finish) before=some after) (later : Run finish after final steps) :
      Run finish before final (steps+1)
theorem Run.trans {finish : Statement C} {before middle final : State C} {early later : Nat}
    (first : Run finish before middle early) (last : Run finish middle final later) : Run finish before final (early+later) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using last
  | step proper edge _ ih => simpa only [Nat.add_right_comm] using Run.step proper edge (ih last)
theorem Run.actual {finish : Statement C} {before final : State C} {steps : Nat} (run : Run finish before final steps) :
    ∃ trace : List (State C),trace.head?=some before ∧ trace.IsChain (fun x y => TM2.step (program finish) x=some y) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧ ∀ current∈trace.dropLast,current.l≠some done := by
  induction run with
  | refl => exact ⟨[_],rfl,List.isChain_singleton _,rfl,rfl,by simp⟩
  | @step before after final steps proper edge _ ih =>
    obtain ⟨trace,first,chain,last,length,interior⟩:=ih
    obtain ⟨tail,rfl⟩:=List.head?_eq_some_iff.mp first
    refine ⟨before::after::tail,rfl,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_,?_⟩
    · change (after::tail).getLast?=some final;exact last
    · simp only [List.length_cons] at length ⊢;omega
    · intro current member
      rw [List.dropLast_cons_cons] at member
      rcases List.mem_cons.mp member with rfl | later
      · exact proper
      · exact interior current later

theorem Run.of_mapped {A : Type*} (finish : Statement C) (mapping : A → State C) (relation : A → A → Prop)
    (trace : List A) (before final : A) (first : trace.head?=some before) (chain : trace.IsChain relation) (last : trace.getLast?=some final)
    (edges : ∀ current∈trace.dropLast,∀ next,relation current next → TM2.step (program finish) (mapping current)=some (mapping next))
    (proper : ∀ current∈trace.dropLast,(mapping current).l≠some done) :
    Run finish (mapping before) (mapping final) (trace.length-1) := by
  induction trace generalizing before with
  | nil => cases first
  | cons head tail ih =>
    have same : head=before := Option.some.inj first
    subst head
    cases tail with
    | nil =>
      have same : before=final := Option.some.inj last
      subst final;exact Run.refl
    | cons next rest =>
      obtain ⟨edge,laterChain⟩:=List.isChain_cons_cons.mp chain
      have later:=ih next rfl laterChain (by exact last)
        (by intro current member other related
            exact edges current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member) other related)
        (by intro current member
            exact proper current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member))
      have now:=Run.step (proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self))
        (edges before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self) next edge) later
      simpa only [List.length_cons,Nat.add_sub_cancel] using now

theorem core_path (finish : Statement C) {before final : DFSDriver.State C} {steps : Nat}
    (path : Path .halt .halt .halt .halt before final steps) :
    Run finish (LabelMap.configuration coreMap before) (LabelMap.configuration coreMap final) steps := by
  obtain ⟨trace,first,chain,last,length,proper⟩:=path.actual
  have run:=Run.of_mapped finish (LabelMap.configuration coreMap)
    (fun x y => TM2.step source x=some y) trace before final first chain last
    (by intro current member next edge
        rw [LabelMap.step_configuration_on coreMap source (program finish) current
          (by intro point active;exact core_code finish point (proper current member point active)),edge]
        rfl)
    (by intro current member
        cases active : current.l with
        | none => change current.l.map coreMap≠some done;rw [active];intro impossible;cases impossible
        | some point =>
          have inside:=proper current member point active
          have mapped : coreMap point=.inl point := by
            simp only [coreMap]
            split_ifs with hg hb hp
            · exact False.elim (inside (Or.inl hg))
            · exact False.elim (inside (Or.inr (Or.inl hb)))
            · exact False.elim (inside (Or.inr (Or.inr (Or.inl hp))))
            · rfl
          change current.l.map coreMap≠some done
          rw [active,Option.map_some,mapped]
          intro same
          have eq : point=rootDone := Sum.inl.inj (Option.some.inj same)
          exact inside (Or.inr (Or.inr (Or.inr eq))))
  rw [length] at run
  simpa only [Nat.add_sub_cancel] using run
end RootB236.Controller.DFSDriver.Machine
