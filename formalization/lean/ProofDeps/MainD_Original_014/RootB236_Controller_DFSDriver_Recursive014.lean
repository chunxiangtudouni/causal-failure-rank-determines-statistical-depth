module
public import RootB236_Controller_DFSDriver_Scan012
public import RootB236_Controller_DFSDriver_Semantics013

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*} {q : Nat}

def returnPort (tail : List Bool) : Label := if tail.isEmpty then done else .inr .popBoot

def pickBits : Option (Fin q) → List Bool | none => [] | some tool => unary tool.val

/-- Only actual data fields are needed across recursive frame restoration. -/
structure Reply (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (tail : List Bool) (context : C) (final : State C) : Prop where
  active : final.l=some (returnPort tail)
  context : final.var.1=context
  spool : final.stk 13=(evaluateCode q limit stages remaining).pick.isSome::tail
  rank : final.stk 15=unary (evaluateCode q limit stages remaining).rank
  tool : final.stk 14=pickBits (evaluateCode q limit stages remaining).pick

/-- An internal staged-data procedure contract, quantified over whole physical memory. -/
def NodeSpec (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q))) (remaining : Finset (Fin q)) : Prop :=
  ∀ (memory : Store C) (before : Stack → List Bool) (flag : Bool) (tail : List Bool),
    before 0=rows q stages → before 2=unary limit → before 4=EraseSem.mask remaining →
    before 11=unary q → before 13=flag::tail →
    ∃ steps final,Run finish (state start memory before) final steps ∧ Reply limit q stages remaining tail memory.1 final

theorem active_state (before : State C) (point : Label) (active : before.l=some point) :
    before=state point before.var before.stk := by
  cases before with
  | mk position memory slots =>
    change position=some point at active
    subst position;rfl

theorem node_bank_eq (before : Stack → List Bool) (input : List Bool) (limit : Nat) (remaining : List Bool)
    (q : Nat) (frame : List Bool) (r0 : before 0=input) (r2 : before 2=unary limit)
    (r4 : before 4=remaining) (r11 : before 11=unary q) (r13 : before 13=frame) :
    nodeBank before input limit remaining q frame=before := by
  funext slot;fin_cases slot
  all_goals first | rfl | exact r0.symm | exact r2.symm | exact r4.symm | exact r11.symm | exact r13.symm

/-- Push, the real recursive run, and the unique runtime-kind-reading pop all use one source. -/
theorem child_call (finish : Statement C) (limit q : Nat) (stages : List (Finset (Fin q)))
    (remaining : Finset (Fin q)) (child : NodeSpec finish limit q stages remaining)
    (memory : Store C) (parent : Stack → List Bool) (kind : Bool)
    (r0 : parent 0=rows q stages) (r2 : parent 2=unary limit)
    (r4 : parent 4=EraseSem.mask remaining) (r11 : parent 11=unary q) :
    ∃ steps order,Run finish (state (.inr (.pushBoot kind)) memory parent)
      (state (.inl (if kind then returnedGood else returnedBad)) (memory.1,false,false,order)
        (B23_6.DFSFrame.restoreBank parent (unary (evaluateCode q limit stages remaining).rank))) steps := by
  obtain ⟨pushed,pushRun,_time⟩:=push finish memory parent kind
  let bank:=B23_6.DFSFrame.pushBank kind parent
  let tail:=B23_6.DFSFrame.framePrefix parent kind 14
  obtain ⟨evaluated,final,childRun,reply⟩:=child (memory.1,false,false,memory.2.2.2) bank false tail
    r0 r2 r4 r11 rfl
  have nested : returnPort tail=.inr .popBoot := by
    have nonempty:=frame_nonempty parent kind
    have notEmpty : tail.isEmpty=false := by
      cases same : tail with
      | nil => exact False.elim (nonempty same)
      | cons head rest => rfl
    simp only [returnPort,notEmpty,Bool.false_eq_true,ite_false]
  have finalState:=active_state final (.inr .popBoot) (by rw [reply.active,nested])
  rw [finalState] at childRun
  obtain ⟨popped,popRun,_popTime⟩:=pop finish final.var parent final.stk kind
    (evaluateCode q limit stages remaining).pick.isSome reply.spool
  rw [reply.rank,reply.context] at popRun
  exact ⟨_,final.var.2.2.2,pushRun.trans (childRun.trans popRun)⟩

/-- Terminal case including N0, q0 and all arbitrary old work banks. -/
theorem terminal_spec (finish : Statement C) (limit q : Nat) (remaining : Finset (Fin q)) :
    NodeSpec finish limit q [] remaining := by
  intro memory before flag tail r0 r2 r4 r11 r13
  have normal:=node_bank_eq before [] limit (EraseSem.mask remaining) q (flag::tail) r0 r2 r4 r11 r13
  have leafPath:=call_nil_path .halt .halt .halt .halt before memory limit (EraseSem.mask remaining) q (flag::tail)
  rw [normal] at leafPath
  have actual:=core_path finish leafPath
  rw [core_state,core_state] at actual
  have out : coreMap (if (flag::tail).tail.isEmpty then rootDone else popFrame)=returnPort tail := by
    simp only [List.tail_cons,returnPort]
    by_cases empty : tail.isEmpty=true
    · simp only [empty,ite_true];rfl
    · simp only [empty];rfl
  rw [out] at actual
  refine ⟨_,_,actual,?_,rfl,rfl,rfl,rfl⟩
  rfl
end RootB236.Controller.DFSDriver.Machine
