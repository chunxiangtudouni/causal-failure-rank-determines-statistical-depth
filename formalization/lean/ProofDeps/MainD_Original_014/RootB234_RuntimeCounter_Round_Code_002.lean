module

public import RootB234_RuntimeCounter_Round_Raw_001
public import Common.PSTR_WordBool_NativeMulCode_057
public import Common.PSTR_WordVM_VirtualBool_025
public import Common.PSTR_WordVM_StackIso_042

/-! Actual 10/11 old-machine call, followed by physical finite-stack
normalization. A real TRUE footer bounds the flagged field. The scanner
copies the real bits to temporary4, consumes the real END00 and TRUE,
clears both residual native stacks, reinstalls guard11, and reverses4 back
to10. No finite-tail equality is inferred from quotient Tape equality. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace RootB234.RuntimeCounter.Round

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PSTRWordVM RationalControllerComputation

abbrev Stack := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev Label := Fin 9
abbrev OldStore := BoolOnStacks.Store Raw.support.card
abbrev Registers := (Bool × Bool) × OldStore
abbrev Store (C : Type*) := C × Registers
abbrev BaseStatement := TM2.Stmt Alphabet Label Registers
abbrev BaseState := TM2.Cfg Alphabet Label Registers
abbrev Statement (C : Type*) := TM2.Stmt Alphabet Label (Store C)
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Store C)

def roles : Stack ≃ Stack := (Equiv.swap 0 10).trans (Equiv.swap 1 11)

def nativeLabel (point : VirtualReturn.Label) : Label := if point=0 then 1 else 2

noncomputable def nativeBody : BaseStatement :=
  LabelMap.statement nativeLabel (StackIso.statement roles
    (VirtualReturn.statement (C := Bool × Bool) (VirtualBool.source Raw.finiteMachine ())))

def capture (memory : Registers) (cell : Option Bool) : Registers :=
  ((cell.isSome,cell.getD false),memory.2)

def bit (memory : Registers) : Bool := memory.1.2
def present (memory : Registers) : Bool := memory.1.1

noncomputable def decoded (memory : Registers) : Raw.Label :=
  PSTRSymbolicRelabel.finiteDecode Raw.support memory.2.1

noncomputable def initialZero (memory : Registers) : Bool :=
  match decoded memory with
  | .halt zero _ => zero
  | _ => false

noncomputable def afterZero (memory : Registers) : Bool :=
  match decoded memory with
  | .halt _ zero => zero
  | _ => false

def jump (point : Label) : BaseStatement := .goto (fun _ => point)

noncomputable def baseProgram (point : Label) : BaseStatement :=
  match point.val with
  | 0 => .load (fun _ => default) (jump 1)
  | 1 => nativeBody
  | 2 => .pop 10 capture (.push 4 bit (.pop 10 capture (.push 4 bit
      (.branch bit (jump 2) (jump 3)))))
  | 3 => .pop 10 capture (.push 4 bit (jump 4))
  | 4 => .pop 10 capture (.branch present (jump 4) (jump 5))
  | 5 => .pop 11 capture (.branch present (jump 5) (.push 11 (fun _ => false) (jump 6)))
  | 6 => .pop 4 capture (.branch present (.push 10 bit (jump 6))
      (.branch initialZero (jump 7) (jump 8)))
  | _ => .halt

noncomputable def program {C : Type*} : Label → Statement C := ContextLift.machine baseProgram

def support : Finset Label := Finset.univ

def cells (frame : Stack → List Bool) (right left scratch : List Bool) : Stack → List Bool :=
  fun slot => if slot=10 then right else if slot=11 then left else if slot=4 then scratch else frame slot

def baseState (frame : Stack → List Bool) (point : Label) (memory : Registers)
    (right left scratch : List Bool) : BaseState := ⟨some point,memory,cells frame right left scratch⟩

def entry {C : Type*} (frame : Stack → List Bool) (memory : Store C) (digits : List Bool) : State C :=
  ⟨some 0,memory,cells frame (Raw.packet digits) [false] []⟩

def Work (slot : Stack) : Prop := slot=4 ∨ slot=10 ∨ slot=11

theorem right_at (frame : Stack → List Bool) (right left scratch : List Bool) : cells frame right left scratch 10=right := rfl
theorem left_at (frame : Stack → List Bool) (right left scratch : List Bool) : cells frame right left scratch 11=left := rfl
theorem scratch_at (frame : Stack → List Bool) (right left scratch : List Bool) : cells frame right left scratch 4=scratch := rfl

theorem update_right (frame : Stack → List Bool) (right left scratch next : List Bool) :
    Function.update (cells frame right left scratch) 10 next=cells frame next left scratch := by
  funext slot; fin_cases slot <;> rfl

theorem update_left (frame : Stack → List Bool) (right left scratch next : List Bool) :
    Function.update (cells frame right left scratch) 11 next=cells frame right next scratch := by
  funext slot; fin_cases slot <;> rfl

theorem update_scratch (frame : Stack → List Bool) (right left scratch next : List Bool) :
    Function.update (cells frame right left scratch) 4 next=cells frame right left next := by
  funext slot; fin_cases slot <;> rfl

theorem cells_frame (frame : Stack → List Bool) (right left scratch : List Bool)
    (slot : Stack) (untouched : ¬Work slot) : cells frame right left scratch slot=frame slot := by
  have n4 : slot≠4 := fun equal => untouched (Or.inl equal)
  have n10 : slot≠10 := fun equal => untouched (Or.inr (Or.inl equal))
  have n11 : slot≠11 := fun equal => untouched (Or.inr (Or.inr equal))
  simp only [cells,n4,n10,n11,ite_false]

theorem capture_old (memory : Registers) (cell : Option Bool) : (capture memory cell).2=memory.2 := rfl

theorem capture_initialZero (memory : Registers) (cell : Option Bool) :
    initialZero (capture memory cell)=initialZero memory := rfl

theorem capture_afterZero (memory : Registers) (cell : Option Bool) :
    afterZero (capture memory cell)=afterZero memory := rfl

theorem program_actions (point : Label) : ScannerClock.actions (program (C := Unit) point)≤4 := by
  rw [program,ContextLift.machine,ContextLift.statement_actions]
  fin_cases point <;> exact of_decide_eq_true rfl

theorem program_pushes (point : Label) : AuxWorkspace.pushes (program (C := Unit) point)≤2 := by
  rw [program,ContextLift.machine,ContextLift.statement_pushes]
  fin_cases point <;> exact of_decide_eq_true rfl

theorem base_actions (point : Label) : ScannerClock.actions (baseProgram point)≤4 :=
  by simpa only [program,ContextLift.machine,ContextLift.statement_actions] using program_actions point

theorem base_pushes (point : Label) : AuxWorkspace.pushes (baseProgram point)≤2 :=
  by simpa only [program,ContextLift.machine,ContextLift.statement_pushes] using program_pushes point

/-- A quotient representation only yields an actual prefix. All remaining
physical cells are retained as a tail and will be consumed by real clear. -/
private theorem blank_extends_true_end (xs ys : List Bool) (last : ys.getLast?=some true)
    (extension : BlankExtends xs ys) : xs=ys := by
  obtain ⟨count,rfl⟩ := extension
  cases count with
  | zero => simp
  | succ count => simp [List.getLast?_append,List.getLast?_replicate] at last

theorem true_ended_prefix (wanted actual : List Bool) (last : wanted.getLast?=some true)
    (represented : ListBlank.mk actual=ListBlank.mk wanted) : ∃ tail,actual=wanted++tail := by
  have related : BlankRel actual wanted := Quotient.exact represented
  rcases related with earlier | later
  · have equal := blank_extends_true_end actual wanted last earlier
    exact ⟨[],by simpa only [List.append_nil] using equal⟩
  · obtain ⟨count,equal⟩ := later
    exact ⟨List.replicate count false,equal⟩

theorem packet_last (digits : List Bool) : (Raw.packet digits).getLast?=some true := by
  simp [Raw.packet]

theorem packet_length (digits : List Bool) : (Raw.packet digits).length=2*digits.length+3 := by
  simp only [Raw.packet,List.length_append,PSTRTMIncrement009.blocks_length,
    List.length_cons,List.length_nil]

end RootB234.RuntimeCounter.Round
