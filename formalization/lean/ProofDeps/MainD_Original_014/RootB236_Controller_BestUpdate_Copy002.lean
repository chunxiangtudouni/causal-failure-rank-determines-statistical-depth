module
public import RootB236_Controller_BestUpdate_Code001

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.BestUpdate
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
/-- Actual steps only. The ACTIVE done body is never executed inside this path. -/
inductive Path (caller : Statement C) : State C → State C → Nat → Prop where
  | refl {current} : Path caller current current 0
  | step {before after final steps} (proper : before.l≠some done)
      (edge : TM2.step (program caller) before=some after) (later : Path caller after final steps) :
      Path caller before final (steps+1)
theorem Path.trans {caller : Statement C} {before middle final : State C} {early later : Nat}
    (first : Path caller before middle early) (last : Path caller middle final later) :
    Path caller before final (early+later) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using last
  | step proper edge _ ih => simpa only [Nat.add_right_comm] using Path.step proper edge (ih last)
theorem Path.actual {caller : Statement C} {before final : State C} {steps : Nat}
    (path : Path caller before final steps) :
    ∃ trace : List (State C),trace.head?=some before ∧
      trace.IsChain (fun x y => TM2.step (program caller) x=some y) ∧
      trace.getLast?=some final ∧ trace.length=steps+1 ∧
      ∀ current∈trace.dropLast,current.l≠some done := by
  induction path with
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
/-- Transport the same legacy chain; no stopped configuration is reset for free. -/
theorem Path.of_mapped {A : Type*} (caller : Statement C) (mapping : A → State C)
    (relation : A → A → Prop) (trace : List A) (before final : A)
    (first : trace.head?=some before) (chain : trace.IsChain relation) (last : trace.getLast?=some final)
    (edges : ∀ current∈trace.dropLast,∀ next,relation current next →
      TM2.step (program caller) (mapping current)=some (mapping next))
    (proper : ∀ current∈trace.dropLast,(mapping current).l≠some done) :
    Path caller (mapping before) (mapping final) (trace.length-1) := by
  induction trace generalizing before with
  | nil => cases first
  | cons head tail ih =>
    have same : head=before := Option.some.inj first
    subst head
    cases tail with
    | nil =>
      have same : before=final := Option.some.inj last
      subst final;exact Path.refl
    | cons next rest =>
      obtain ⟨edge,laterChain⟩:=List.isChain_cons_cons.mp chain
      have later:=ih next rfl laterChain (by exact last)
        (by intro current member other related
            exact edges current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member) other related)
        (by intro current member
            exact proper current (by rw [List.dropLast_cons_cons];exact List.mem_cons_of_mem _ member))
      have now:=Path.step (proper before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self))
        (edges before (by rw [List.dropLast_cons_cons];exact List.mem_cons_self) next edge) later
      simpa only [List.length_cons,Nat.add_sub_cancel] using now

def copyLocal (tool : Bool) (point : B23_4_RatWordPrep.WholeCopy.Label) :
    TM2.Stmt Alphabet B23_4_RatWordPrep.WholeCopy.Label (Store C) :=
  StackIso.statement (copyRoles tool)
    (StoreIso.statement storeIso (B23_4_RatWordPrep.WholeCopy.program .halt point))
def copyConfiguration (tool : Bool)
    (old : B23_4_RatWordPrep.WholeCopy.State (C×Ordering)) : State C :=
  LabelMap.configuration (copyMap tool)
    (StackIso.configuration (copyRoles tool) (StoreIso.configuration storeIso old))
def copyBank (tool : Bool) (background : Stack → List Bool) (input backup scratch : List Bool) : Stack → List Bool :=
  fun slot => if slot=copyRoles tool 0 then input else if slot=copyRoles tool 2 then backup
    else if slot=copyRoles tool 3 then scratch else background slot
def copyState (tool : Bool) (background : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup scratch : List Bool) : State C :=
  state (copyMap tool point) memory (copyBank tool background input backup scratch)
theorem copyBank_eq (tool : Bool) (bg : Stack → List Bool) (input backup scratch : List Bool) :
    copyBank tool bg input backup scratch=StackIso.slots (copyRoles tool)
      (B23_4_RatWordPrep.WholeCopy.bank (StackIso.slots (copyRoles tool).symm bg) input backup scratch) := by
  funext slot
  simp only [copyBank,StackIso.slots,B23_4_RatWordPrep.WholeCopy.bank,Equiv.symm_apply_eq,
    Equiv.symm_symm,Equiv.apply_symm_apply]
theorem copyState_eq (tool : Bool) (bg : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup scratch : List Bool) :
    copyState tool bg point memory input backup scratch=copyConfiguration tool
      (B23_4_RatWordPrep.WholeCopy.state (StackIso.slots (copyRoles tool).symm bg) point
        (storeIso.symm memory) input backup scratch) := by
  rw [copyState,copyBank_eq]
  simp only [state,copyConfiguration,LabelMap.configuration,StackIso.configuration,
    StoreIso.configuration,B23_4_RatWordPrep.WholeCopy.state,Equiv.apply_symm_apply,Option.map_some]
theorem copy_edge (caller : Statement C) (tool : Bool)
    (before after : B23_4_RatWordPrep.WholeCopy.State (C×Ordering))
    (proper : before.l≠some .done)
    (edge : TM2.step (B23_4_RatWordPrep.WholeCopy.program .halt) before=some after) :
    TM2.step (program caller) (copyConfiguration tool before)=some (copyConfiguration tool after) := by
  have code : ∀ point,(StackIso.configuration (copyRoles tool) (StoreIso.configuration storeIso before)).l=some point →
      program caller (copyMap tool point)=LabelMap.statement (copyMap tool) (copyLocal tool point) := by
    intro point active
    exact copy_code caller tool point (by intro same;subst point;exact proper active)
  unfold copyConfiguration
  rw [LabelMap.step_configuration_on (copyMap tool) (copyLocal tool) (program caller) _ code]
  rw [StackIso.step_configuration_on (copyRoles tool)
    (StoreIso.machine storeIso (B23_4_RatWordPrep.WholeCopy.program .halt)) (copyLocal tool) _ (by intros;rfl)]
  rw [StoreIso.step_configuration storeIso (B23_4_RatWordPrep.WholeCopy.program .halt),edge]
  rfl

theorem actual_copy (caller : Statement C) (tool : Bool) (bg : Stack → List Bool) (memory : Store C)
    (input backup scratch : List Bool) :
    Path caller (copyState tool bg .boot memory input backup scratch)
      (copyState tool bg .done (memory.1,true,true,memory.2.2.2) input (input.reverse++backup) scratch)
      (2*input.length+3) := by
  obtain ⟨trace,facts⟩:=B23_4_RatWordPrep.WholeCopy.actual_bounded
    (StackIso.slots (copyRoles tool).symm bg) (storeIso.symm memory) input backup scratch
  have noEarly : ∀ current∈trace.dropLast,current.l≠some B23_4_RatWordPrep.WholeCopy.Label.done := by
    intro current member;exact (facts.proper current member).1
  have path:=Path.of_mapped caller (copyConfiguration tool)
    (fun x y => TM2.step (B23_4_RatWordPrep.WholeCopy.program .halt) x=some y)
    trace _ _ facts.first facts.chain facts.last
    (by intro current member next edge;exact copy_edge caller tool current next (noEarly current member) edge)
    (by intro current member
        have proper:=noEarly current member
        cases current with
        | mk position registers slots =>
          cases position with
          | none => simp only [copyConfiguration,LabelMap.configuration,StackIso.configuration,StoreIso.configuration,Option.map_none];intro impossible;cases impossible
          | some point =>
            cases tool <;> cases point <;> simp_all [copyConfiguration,LabelMap.configuration,
              StackIso.configuration,StoreIso.configuration,copyMap,done])
  rw [facts.count] at path
  have finalStore : storeIso.symm (memory.1,true,true,memory.2.2.2)=((storeIso.symm memory).1,true,true) := rfl
  rw [←copyState_eq] at path
  rw [←finalStore,←copyState_eq] at path
  exact path
end RootB236.Controller.BestUpdate
