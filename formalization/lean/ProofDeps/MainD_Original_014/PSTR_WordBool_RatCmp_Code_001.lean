module

public import PSTR_WordBool_RatAddSub_Callees_001

/-! Fixed finite Bool packet reader for the actual subtraction result.
It pops only its newly prepended packet and pushes one physical result
bit on3. No rational value or length is an executable parameter. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordBool.RatCmp.Reader

open Turing PSTRWordVM RationalControllerComputation

abbrev Stack := RatOutput.Stack
abbrev Label := Fin 5
abbrev Store := Bool × Bool × Bool
abbrev Statement (C : Type*) := TM2.Stmt RatOutput.Alphabet Label (C × Store)
abbrev State (C : Type*) := TM2.Cfg RatOutput.Alphabet Label (C × Store)

variable {C : Type*}

def captureSign (memory : C × Store) (value : Option Bool) : C × Store :=
  (memory.1,(value.getD false,false,memory.2.2.2))
def captureFlag (memory : C × Store) (value : Option Bool) : C × Store :=
  (memory.1,(memory.2.1,memory.2.2.1,value.getD false))
def captureNum (memory : C × Store) (value : Option Bool) : C × Store :=
  (memory.1,(memory.2.1,memory.2.2.1 || value.getD false,memory.2.2.2))
def keep (memory : C × Store) (_ : Option Bool) : C × Store := memory
def flag (memory : C × Store) : Bool := memory.2.2.2
def result (memory : C × Store) : Bool := memory.2.1 || !(memory.2.2.1)

def program (caller : Statement C) (point : Label) : Statement C :=
  if point=0 then .pop 15 keep (.pop 15 captureSign (.goto (fun _=>1)))
  else if point=1 then .pop 15 captureFlag (.branch flag
    (.pop 15 captureNum (.goto (fun _=>1))) (.pop 15 keep (.goto (fun _=>2))))
  else if point=2 then .pop 15 captureFlag (.branch flag
    (.pop 15 keep (.goto (fun _=>2))) (.pop 15 keep (.goto (fun _=>3))))
  else if point=3 then .push 3 result (.goto (fun _=>4)) else caller

def cells (background : Stack → List Bool) (source target : List Bool) : Stack → List Bool :=
  fun slot=>if slot=15 then source else if slot=3 then target else background slot

def state (background : Stack → List Bool) (point : Label) (context : C) (memory : Store)
    (source target : List Bool) : State C := ⟨some point,(context,memory),cells background source target⟩

theorem source_at (background : Stack → List Bool) (source target : List Bool) : cells background source target 15=source := rfl
theorem target_at (background : Stack → List Bool) (source target : List Bool) : cells background source target 3=target := rfl
theorem update_source (background : Stack → List Bool) (source target next : List Bool) :
    Function.update (cells background source target) 15 next=cells background next target := by
  funext slot;fin_cases slot <;> rfl
theorem update_target (background : Stack → List Bool) (source target next : List Bool) :
    Function.update (cells background source target) 3 next=cells background source next := by
  funext slot;fin_cases slot <;> rfl

theorem start_step (caller : Statement C) (background : Stack → List Bool) (context : C) (memory : Store)
    (negative : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 0 context memory (true::negative::source) target)=
      some (state background 1 context (negative,false,memory.2.2) source target) := by
  simp [program,state,TM2.step,TM2.stepAux,keep,captureSign,source_at,update_source]

theorem num_step (caller : Statement C) (background : Stack → List Bool) (context : C)
    (negative seen oldFlag bit : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 1 context (negative,seen,oldFlag) (true::bit::source) target)=
      some (state background 1 context (negative,seen || bit,true) source target) := by
  simp [program,state,TM2.step,TM2.stepAux,captureFlag,captureNum,flag,source_at,update_source]

theorem num_end (caller : Statement C) (background : Stack → List Bool) (context : C)
    (negative seen oldFlag : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 1 context (negative,seen,oldFlag) (false::false::source) target)=
      some (state background 2 context (negative,seen,false) source target) := by
  simp [program,state,TM2.step,TM2.stepAux,captureFlag,keep,flag,source_at,update_source]

theorem den_step (caller : Statement C) (background : Stack → List Bool) (context : C)
    (negative seen oldFlag bit : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 2 context (negative,seen,oldFlag) (true::bit::source) target)=
      some (state background 2 context (negative,seen,true) source target) := by
  simp [program,state,TM2.step,TM2.stepAux,captureFlag,keep,flag,source_at,update_source]

theorem den_end (caller : Statement C) (background : Stack → List Bool) (context : C)
    (negative seen oldFlag : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 2 context (negative,seen,oldFlag) (false::false::source) target)=
      some (state background 3 context (negative,seen,false) source target) := by
  simp [program,state,TM2.step,TM2.stepAux,captureFlag,keep,flag,source_at,update_source]

theorem finish_step (caller : Statement C) (background : Stack → List Bool) (context : C)
    (negative seen : Bool) (source target : List Bool) :
    TM2.step (program caller) (state background 3 context (negative,seen,false) source target)=
      some (state background 4 context (negative,seen,false) source ((negative || !seen)::target)) := by
  simp [program,state,TM2.step,TM2.stepAux,result,target_at,update_target]

end PaperProofs.Common.Native.PSTRWordBool.RatCmp.Reader
