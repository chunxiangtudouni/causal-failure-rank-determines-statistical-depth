module
public import Common.PSTR_WordBool_BitwiseCost_070
public import Common.PSTR_WordVM_StackIso_042
public import Common.PSTR_WordBool_ContextLift_041

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
@[expose] public section
namespace RootB236.ControllerCandidate
open Turing
open PaperProofs.Common.Native
open PSTRWordBool
abbrev Stack := Fin 16
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Bool × Bool
inductive ScanLabel where
  | clear | scan | copy | restore | found | empty
  deriving DecidableEq, Inhabited
instance : Fintype ScanLabel where
  elems := {.clear,.scan,.copy,.restore,.found,.empty}
  complete := by intro label; cases label <;> decide
abbrev ScanStatement := TM2.Stmt Alphabet ScanLabel Store
abbrev ScanState := TM2.Cfg Alphabet ScanLabel Store

/-- Runtime counters are stack data. Only presence/value flags enter store. -/
def capture (_ : Store) (value : Option Bool) : Store := (value.isSome,value.getD false)

/-- Both return labels are ACTIVE ports; neither is executed by the leaf run. -/
def scanner : ScanLabel → ScanStatement
  | .clear => .pop 5 capture (.branch Prod.fst
      (.goto (fun _ => .clear)) (.goto (fun _ => .scan)))
  | .scan => .pop 3 capture (.branch Prod.fst
      (.branch Prod.snd (.goto (fun _ => .copy))
        (.push 6 (fun _ => true) (.goto (fun _ => .scan))))
      (.goto (fun _ => .empty)))
  | .copy => .pop 6 capture (.branch Prod.fst
      (.push 5 (fun _ => true) (.push 7 (fun _ => true) (.goto (fun _ => .copy))))
      (.goto (fun _ => .restore)))
  | .restore => .pop 7 capture (.branch Prod.fst
      (.push 6 (fun _ => true) (.goto (fun _ => .restore)))
      (.push 6 (fun _ => true) (.goto (fun _ => .found))))
  | .found | .empty => .halt

def unary (n : Nat) : List Bool := List.replicate n true
def cells (background : Stack → List Bool) (bits result cursor scratch : List Bool) : Stack → List Bool :=
  fun point => if point=3 then bits else if point=5 then result else
    if point=6 then cursor else if point=7 then scratch else background point
def state (background : Stack → List Bool) (label : ScanLabel) (memory : Store)
    (bits result cursor scratch : List Bool) : ScanState :=
  ⟨some label,memory,cells background bits result cursor scratch⟩
def Proper (label : ScanLabel) : Prop := label≠.found ∧ label≠.empty
def Allowed (point : Stack) : Prop := point=3 ∨ point=5 ∨ point=6 ∨ point=7
def Valid (background : Stack → List Bool) (bound : Nat) (current : ScanState) : Prop :=
  (∀ point, (current.stk point).length≤(background point).length+bound) ∧
    ∀ point, ¬Allowed point → current.stk point=background point

theorem valid_state (background : Stack → List Bool) (label : ScanLabel) (memory : Store)
    (bits result cursor scratch : List Bool) (bound : Nat)
    (hb : bits.length≤bound) (hr : result.length≤bound)
    (hc : cursor.length≤bound) (hs : scratch.length≤bound) :
    Valid background bound (state background label memory bits result cursor scratch) := by
  constructor
  · intro point
    fin_cases point <;> simp only [state,cells] <;> norm_num <;> omega
  · intro point outside
    have h3 : point≠3 := fun h => outside (Or.inl h)
    have h5 : point≠5 := fun h => outside (Or.inr (Or.inl h))
    have h6 : point≠6 := fun h => outside (Or.inr (Or.inr (Or.inl h)))
    have h7 : point≠7 := fun h => outside (Or.inr (Or.inr (Or.inr h)))
    simp only [state,cells,h3,h5,h6,h7,ite_false]

theorem step_clear (bg : Stack → List Bool) (mem : Store) (bits old cur : List Bool) (bit : Bool) :
    TM2.step scanner (state bg .clear mem bits (bit::old) cur [])=
      some (state bg .clear (true,bit) bits old cur []) := by
  change some (⟨some .clear,(true,bit),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> rfl
theorem step_clear_end (bg : Stack → List Bool) (mem : Store) (bits cur : List Bool) :
    TM2.step scanner (state bg .clear mem bits [] cur [])=
      some (state bg .scan (false,false) bits [] cur []) := by
  change some (⟨some .scan,(false,false),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> rfl
theorem step_skip (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (k : Nat) :
    TM2.step scanner (state bg .scan mem (false::bits) [] (unary k) [])=
      some (state bg .scan (true,false) bits [] (unary (k+1)) []) := by
  change some (⟨some .scan,(true,false),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> simp [cells,unary,List.replicate_succ]
theorem step_hit (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (k : Nat) :
    TM2.step scanner (state bg .scan mem (true::bits) [] (unary k) [])=
      some (state bg .copy (true,true) bits [] (unary k) []) := by
  change some (⟨some .copy,(true,true),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> rfl
theorem step_empty (bg : Stack → List Bool) (mem : Store) (k : Nat) :
    TM2.step scanner (state bg .scan mem [] [] (unary k) [])=
      some (state bg .empty (false,false) [] [] (unary k) []) := by
  change some (⟨some .empty,(false,false),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> rfl
theorem step_copy (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (rest made : Nat) :
    TM2.step scanner (state bg .copy mem bits (unary made) (unary (rest+1)) (unary made))=
      some (state bg .copy (true,true) bits (unary (made+1)) (unary rest) (unary (made+1))) := by
  simp only [unary,List.replicate_succ]
  change some (⟨some .copy,(true,true),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> simp [cells]
theorem step_copy_end (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (made : Nat) :
    TM2.step scanner (state bg .copy mem bits (unary made) [] (unary made))=
      some (state bg .restore (false,false) bits (unary made) [] (unary made)) := by
  change some (⟨some .restore,(false,false),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> rfl
theorem step_restore (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (tool rest copied : Nat) :
    TM2.step scanner (state bg .restore mem bits (unary tool) (unary copied) (unary (rest+1)))=
      some (state bg .restore (true,true) bits (unary tool) (unary (copied+1)) (unary rest)) := by
  simp only [unary,List.replicate_succ]
  change some (⟨some .restore,(true,true),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> simp [cells]
theorem step_restore_end (bg : Stack → List Bool) (mem : Store) (bits : List Bool) (tool copied : Nat) :
    TM2.step scanner (state bg .restore mem bits (unary tool) (unary copied) [])=
      some (state bg .found (false,false) bits (unary tool) (unary (copied+1)) []) := by
  change some (⟨some .found,(false,false),_⟩ : ScanState)=_
  congr 1; congr 1
  funext point; fin_cases point <;> simp [cells,unary,List.replicate_succ]

theorem scanner_counts (label : ScanLabel) :
    ScannerClock.actions (scanner label)≤3 ∧ AuxWorkspace.pushes (scanner label)≤2 := by
  cases label <;> norm_num [scanner,ScannerClock.actions,AuxWorkspace.pushes]
theorem scanner_writes (label : ScanLabel) : PSTRWordVM.StackIso.WritesOnly Allowed (scanner label) := by
  cases label <;> simp [scanner,PSTRWordVM.StackIso.WritesOnly,Allowed]
end RootB236.ControllerCandidate
