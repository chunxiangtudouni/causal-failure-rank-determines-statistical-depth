module
public import RootB236_Controller_DFSDriver_Callees003

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver
open Turing PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.PSTRWordVM
variable {C : Type*}
def unary := RankCompare.unary

def copyBank (phase : CopyPhase) (bg : Stack → List Bool) (input backup scratch : List Bool) : Stack → List Bool :=
  fun slot => if slot=copyRoles phase 0 then input else if slot=copyRoles phase 2 then backup
    else if slot=copyRoles phase 3 then scratch else bg slot
def copyState (phase : CopyPhase) (bg : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup scratch : List Bool) : State C :=
  state (copyMap phase point) memory (copyBank phase bg input backup scratch)
theorem copy_bank_eq (phase : CopyPhase) (bg : Stack → List Bool) (input backup scratch : List Bool) :
    copyBank phase bg input backup scratch=StackIso.slots (copyRoles phase)
      (B23_4_RatWordPrep.WholeCopy.bank (StackIso.slots (copyRoles phase).symm bg) input backup scratch) := by
  funext slot
  simp only [copyBank,StackIso.slots,B23_4_RatWordPrep.WholeCopy.bank,Equiv.symm_apply_eq,
    Equiv.symm_symm,Equiv.apply_symm_apply]
theorem copy_state_eq (phase : CopyPhase) (bg : Stack → List Bool) (point : B23_4_RatWordPrep.WholeCopy.Label)
    (memory : Store C) (input backup scratch : List Bool) :
    copyState phase bg point memory input backup scratch=transported (copyRoles phase) BestUpdate.storeIso (copyMap phase)
      (B23_4_RatWordPrep.WholeCopy.state (StackIso.slots (copyRoles phase).symm bg) point
        (BestUpdate.storeIso.symm memory) input backup scratch) := by
  rw [copyState,copy_bank_eq]
  simp only [state,transported,LabelMap.configuration,StackIso.configuration,StoreIso.configuration,
    B23_4_RatWordPrep.WholeCopy.state,Equiv.apply_symm_apply,Option.map_some]
theorem copy_current (good bad pop finish : Statement C) (phase : CopyPhase) (bg : Stack → List Bool)
    (memory : Store C) (input backup scratch : List Bool) :
    Path good bad pop finish (copyState phase bg .boot memory input backup scratch)
      (copyState phase bg .done (memory.1,true,true,memory.2.2.2) input (input.reverse++backup) scratch) (2*input.length+3) := by
  obtain ⟨_trace,_facts,path⟩:=copy_path good bad pop finish phase
    (StackIso.slots (copyRoles phase).symm bg) (BestUpdate.storeIso.symm memory) input backup scratch
  have finalStore : BestUpdate.storeIso.symm (memory.1,true,true,memory.2.2.2)=
      ((BestUpdate.storeIso.symm memory).1,true,true) := rfl
  rw [←copy_state_eq] at path
  rw [←finalStore,←copy_state_eq] at path
  exact path

def rowBank (bg : Stack → List Bool) (input eligible : List Bool) (counter : Nat) (parked : List Bool) : Stack → List Bool :=
  fun slot => if slot=0 then input else if slot=3 then eligible else if slot=6 then unary counter else
    if slot=7 then parked else bg slot

theorem read_bit (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (value : Bool) (input eligible parked : List Bool) (counter : Nat) :
    TM2.step (program good bad pop finish) (state (.control 12) memory (rowBank bg (value::input) eligible (counter+1) parked))=
      some (state (.control 12) (memory.1,true,value,memory.2.2.2) (rowBank bg input eligible counter (value::parked))) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem read_end (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (input eligible parked : List Bool) :
    TM2.step (program good bad pop finish) (state (.control 12) memory (rowBank bg input eligible 0 parked))=
      some (state (.control 13) (memory.1,false,memory.2.2.1,memory.2.2.2) (rowBank bg input eligible 0 parked)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl

theorem restore_bit (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (value : Bool) (input eligible parked : List Bool) :
    TM2.step (program good bad pop finish) (state (.control 13) memory (rowBank bg input eligible 0 (value::parked)))=
      some (state (.control 13) (memory.1,true,value,memory.2.2.2) (rowBank bg input (value::eligible) 0 parked)) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem restore_end (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (input eligible : List Bool) :
    TM2.step (program good bad pop finish) (state (.control 13) memory (rowBank bg input eligible 0 []))=
      some (state pushGood (memory.1,false,false,memory.2.2.2) (rowBank bg input eligible 0 [])) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl

theorem read_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (bits suffix eligible parked : List Bool) :
    ∃ finalMemory,Path good bad pop finish
      (state (.control 12) memory (rowBank bg (bits++suffix) eligible bits.length parked))
      (state (.control 13) finalMemory (rowBank bg suffix eligible 0 (bits.reverse++parked))) (bits.length+1) ∧
      finalMemory.1=memory.1 ∧ finalMemory.2.2.2=memory.2.2.2 := by
  induction bits generalizing memory parked with
  | nil =>
    exact ⟨_,Path.step (inside_control _ memory _ (Or.inl (by decide)))
      (read_end good bad pop finish bg memory suffix eligible parked) .refl,rfl,rfl⟩
  | cons value bits ih =>
    obtain ⟨finalMemory,later,context,order⟩:=ih (memory.1,true,value,memory.2.2.2) (value::parked)
    have whole:=Path.step (inside_control _ memory _ (Or.inl (by decide)))
      (read_bit good bad pop finish bg memory value (bits++suffix) eligible parked bits.length) later
    refine ⟨finalMemory,?_,context,order⟩
    simpa only [List.length_cons,List.cons_append,List.reverse_cons,List.append_assoc,List.singleton_append,List.nil_append] using whole

theorem restore_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (input eligible parked : List Bool) :
    Path good bad pop finish (state (.control 13) memory (rowBank bg input eligible 0 parked))
      (state pushGood (memory.1,false,false,memory.2.2.2) (rowBank bg input (parked.reverse++eligible) 0 [])) (parked.length+1) := by
  induction parked generalizing memory eligible with
  | nil =>
    exact Path.step (inside_control _ memory _ (Or.inl (by decide)))
      (restore_end good bad pop finish bg memory input eligible) .refl
  | cons value parked ih =>
    have later:=ih (memory.1,true,value,memory.2.2.2) (value::eligible)
    have whole:=Path.step (inside_control _ memory _ (Or.inl (by decide)))
      (restore_bit good bad pop finish bg memory value input eligible parked) later
    simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using whole

theorem row_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C)
    (bits suffix : List Bool) :
    Path good bad pop finish (state (.control 12) memory (rowBank bg (bits++suffix) [] bits.length []))
      (state pushGood (memory.1,false,false,memory.2.2.2) (rowBank bg suffix bits 0 [])) (2*bits.length+2) := by
  obtain ⟨finalMemory,read,context,order⟩:=read_path good bad pop finish bg memory bits suffix [] []
  simp only [List.append_nil] at read
  have restored:=restore_path good bad pop finish bg finalMemory suffix [] bits.reverse
  rw [context,order] at restored
  have whole:=read.trans restored
  simpa only [List.reverse_reverse,List.append_nil,List.length_reverse,
    show bits.length+1+(bits.length+1)=2*bits.length+2 by omega] using whole

/-- Real return-tail probe. FALSE frame bytes count as present; child hasBest is restored before dispatch. -/
theorem return_probe (good bad pop finish : Statement C) (slots : Stack → List Bool) (memory : Store C)
    (flag : Bool) (tail : List Bool) (represented : slots 13=flag::tail) :
    TM2.step (program good bad pop finish) (state (.control 21) memory slots)=
      some (state (if tail.isEmpty then rootDone else popFrame)
        (memory.1,(!tail.isEmpty),flag,memory.2.2.2) slots) := by
  have unchanged : Function.update slots 13 (flag::tail)=slots := by
    funext slot
    by_cases same : slot=13
    · subst slot;simp only [Function.update_self];exact represented.symm
    · simp only [Function.update_of_ne same]
  cases tail <;>
    simp [state,TM2.step,program,TM2.stepAux,capture,BestUpdate.capturePresent,represented,unchanged]

/-- One real unary rank cell is moved; no host rank assignment occurs. -/
theorem park_bit (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C) (a b : Nat) :
    TM2.step (program good bad pop finish) (state (.control 20) memory
      (Function.update (Function.update bg 9 (unary (a+1))) 15 (unary b)))=
      some (state (.control 20) (memory.1,true,true,memory.2.2.2)
        (Function.update (Function.update bg 9 (unary a)) 15 (unary (b+1)))) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem park_end (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C) (b : Nat) :
    TM2.step (program good bad pop finish) (state (.control 20) memory
      (Function.update (Function.update bg 9 []) 15 (unary b)))=
      some (state (.control 21) (memory.1,false,false,memory.2.2.2)
        (Function.update (Function.update bg 9 []) 15 (unary b))) := by
  change some (⟨_,_,_⟩ : State C)=_
  congr 1;congr 1;funext slot;fin_cases slot <;> rfl
theorem park_path (good bad pop finish : Statement C) (bg : Stack → List Bool) (memory : Store C) (a b : Nat) :
    Path good bad pop finish (state (.control 20) memory (Function.update (Function.update bg 9 (unary a)) 15 (unary b)))
      (state (.control 21) (memory.1,false,false,memory.2.2.2)
        (Function.update (Function.update bg 9 []) 15 (unary (a+b)))) (a+1) := by
  induction a generalizing memory b with
  | zero =>
    simpa only [Nat.zero_add,unary,RankCompare.unary,List.replicate_zero] using (Path.step (inside_control _ memory _ (Or.inr (by decide)))
      (park_end good bad pop finish bg memory b) (Path.refl))
  | succ a ih =>
    have later:=ih (memory.1,true,true,memory.2.2.2) (b+1)
    have whole:=Path.step (inside_control _ memory _ (Or.inr (by decide)))
      (park_bit good bad pop finish bg memory a b) later
    simpa only [show a+(b+1)=a+1+b by omega] using whole
end RootB236.Controller.DFSDriver
