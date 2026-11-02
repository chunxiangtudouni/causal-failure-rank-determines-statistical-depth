module

public import Paid.PDROC_BitVM_Kernel_Branch_011
public import Paid.PDROC_BitVM_Native_Return_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.Control

open Turing PaperProofs.Paid.Computation PDROC.BitVM.Native
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Label := Fin 5
abbrev Store := Branch.Store × Unit
abbrev State := TM2.Cfg Alphabet Label Store

/-- The source register is fixed by source code. Labels2/3 are genuine
zero/nonzero exits;4 is the actual invalid-type exit. All data bytes are
restored before the real branch is taken. -/
def program (condition : Register) (label : Label) : TM2.Stmt Alphabet Label Store :=
  if label=0 then Inline.statement (fun _ : Unit=>(0 : Label)) 1 (Branch.program (registerSlot condition) ())
  else if label=1 then
    .branch (fun store=>store.1.1==some false)
      (.branch (fun store=>Branch.zeroFlag store.1) (.goto (fun _=>2)) (.goto (fun _=>3)))
      (.goto (fun _=>4))
  else .halt

def before (contents : Stack → List Bool) (store : Branch.Store) : State :=
  ⟨some 0,(store,()),contents⟩

def inspected (condition : Register) (contents : Stack → List Bool) : State :=
  ⟨some 1,(Branch.captured (contents (registerSlot condition)),()),contents⟩

def exitLabel (value : ℕ) : Label := if value=0 then 2 else 3

def reached (condition : Register) (contents : Stack → List Bool) (value : ℕ) : State :=
  ⟨some (exitLabel value),(Branch.captured (contents (registerSlot condition)),()),contents⟩

theorem read_agrees (condition : Register) : ∀ label : Unit,
    program condition ((fun _ : Unit=>(0 : Label)) label)=
      Inline.statement (fun _ : Unit=>(0 : Label)) 1 (Branch.program (registerSlot condition) label) := by
  intro label
  cases label
  rfl

theorem natural_branch (condition : Register) (contents : Stack → List Bool) (value : ℕ)
    (word : contents (registerSlot condition)=encodeCellBits (.natural value)) :
    TM2.step (program condition) (inspected condition contents)=some (reached condition contents value) := by
  have tag : (Branch.captured (contents (registerSlot condition))).1=some false := by rw [word];rfl
  have flag : Branch.zeroFlag (Branch.captured (contents (registerSlot condition)))=decide (value=0) := by
    rw [word]
    exact Branch.natural_zero value
  by_cases zero : value=0 <;> simp [program,inspected,reached,exitLabel,tag,flag,zero,TM2.step,TM2.stepAux]

/-- ONE actual register-read/restore/conditional-goto path. Its chosen
finite exit is proved equal to the original Nat zero predicate; the caller
connects these compile-time exits to its original program-counter labels. -/
theorem branch_runs (condition : Register) (contents : Stack → List Bool) (store : Branch.Store) (value : ℕ)
    (word : contents (registerSlot condition)=encodeCellBits (.natural value)) :
    ∃ run : List State,run.head?=some (before contents store) ∧ 
      run.IsChain (fun a b=>TM2.step (program condition) a=some b) ∧ 
      run.getLast?=some (reached condition contents value) ∧ run.length=3 ∧ 
      (reached condition contents value).l=some (exitLabel value) ∧ 
      (reached condition contents value).stk=contents := by
  obtain ⟨source,head,chain,last,halt,length⟩ := Branch.runs (registerSlot condition) contents store
  obtain ⟨run,returned,first,actual,finish,atReturn,data,saved,size⟩ :=
    Inline.actual_return_trace (fun _ : Unit=>(0 : Label)) 1 (Branch.program (registerSlot condition))
      (program condition) (read_agrees condition) source
      (⟨some (),store,contents⟩ : Branch.State)
      (⟨none,Branch.captured (contents (registerSlot condition)),contents⟩ : Branch.State) () head chain last halt
  have returnedEq : returned=inspected condition contents := by
    rcases returned with ⟨label,finiteStore,physical⟩
    change label=some 1 at atReturn
    change finiteStore=(Branch.captured (contents (registerSlot condition)),()) at saved
    change physical=contents at data
    subst label
    subst finiteStore
    subst physical
    rfl
  have edge : TM2.step (program condition) returned=some (reached condition contents value) := by
    rw [returnedEq]
    exact natural_branch condition contents value word
  have pair : [returned,reached condition contents value].IsChain
      (fun a b=>TM2.step (program condition) a=some b) :=
    List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩
  refine ⟨run++[reached condition contents value],?_,
    PaperProofs.Common.Native.PSTRWordBool.NativeTrace.join_chain _ _ _ finish actual pair,
    List.getLast?_append_cons run (reached condition contents value) [],?_,rfl,rfl⟩
  · simp only [List.head?_append,first,Option.some_or]
    rfl
  · simp only [List.length_append,List.length_cons,List.length_nil,size,length]

theorem original_branch_execute (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (condition : Register) (whenZero whenNonzero value : ℕ)
    (natural : logical.register condition=.natural value) :
    Instruction.execute input (.branchZero condition whenZero whenNonzero) logical=
      some {logical with pc:=if value=0 then whenZero else whenNonzero} := by
  simp [Instruction.execute,natural,Cell.nat?]

theorem rational_invalid (condition : Register) (contents : Stack → List Bool) (value : ℚ)
    (word : contents (registerSlot condition)=encodeCellBits (.rational value)) :
    TM2.step (program condition) (inspected condition contents)=
      some (⟨some 4,(Branch.captured (contents (registerSlot condition)),()),contents⟩ : State) := by
  have tag : (Branch.captured (contents (registerSlot condition))).1=some true := by rw [word];rfl
  simp [program,inspected,TM2.step,TM2.stepAux,tag]

theorem supports (condition : Register) : TM2.Supports (program condition) (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · exact Inline.supports_statement (fun _ : Unit=>(0 : Label)) 1 Finset.univ Finset.univ
        (fun _ _=>Finset.mem_univ _) (Finset.mem_univ _) (Branch.program (registerSlot condition) ())
        ((Branch.supports (registerSlot condition)).2 () (Finset.mem_univ _))
    · simp [program,TM2.SupportsStmt]
    · trivial
    · trivial
    · trivial

end PDROC.BitVM.Kernel.Control
