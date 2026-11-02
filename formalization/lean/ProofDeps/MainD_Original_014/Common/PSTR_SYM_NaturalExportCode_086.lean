module

public import Mathlib.Computability.TuringMachine.StackTuringMachine
public import Mathlib.Data.List.Chain
public import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Omega

/-! Actual finite paired-natural exporter. Slot1 is walked and restored;
slot7 owns a genuinely pushed TRUE sentinel with [FALSE,cell] backups.
Slot15 receives blocks(payload)++[FALSE,FALSE] before its arbitrary old
tail, so no consumer needs a host length or empty destination. No Nat
value/width occurs in code or its three-Boolean temporary store. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport

open Turing

abbrev Slot := Fin 16
abbrev Label := Fin 5
abbrev Alphabet (_ : Slot) := Bool
abbrev Store := Bool × Bool × Bool
abbrev Memory (C : Type*) := C × Store
abbrev State (C : Type*) := TM2.Cfg Alphabet Label (Memory C)

def savedBit {C : Type*} (memory : Memory C) : Bool := memory.2.1
def savedFlag {C : Type*} (memory : Memory C) : Bool := memory.2.2.1
def positive {C : Type*} (memory : Memory C) : Bool := memory.2.2.2

def captureBit {C : Type*} (memory : Memory C) (value : Option Bool) : Memory C :=
  (memory.1,(value.getD false,memory.2.2))

def captureFlag {C : Type*} (memory : Memory C) (value : Option Bool) : Memory C :=
  (memory.1,(memory.2.1,(value.getD true,memory.2.2.2)))

def captureMode {C : Type*} (memory : Memory C) (value : Option Bool) : Memory C :=
  (memory.1,(memory.2.1,(memory.2.2.1,value.getD false)))

def program {C : Type*} (label : Label) : TM2.Stmt Alphabet Label (Memory C) :=
  if label = 0 then
    .push 7 (fun _ => true)
      (.push 15 (fun _ => false) (.push 15 (fun _ => false)
        (.pop 1 captureBit
          (.push 7 savedBit (.push 7 (fun _ => false)
            (.pop 1 captureMode
              (.push 7 positive (.push 7 (fun _ => false)
                (.branch positive (.goto (fun _ => 1)) (.goto (fun _ => 2)))))))))))
  else if label = 1 then
    .pop 1 captureBit (.peek 1 captureFlag
      (.branch savedFlag
        (.push 1 savedBit (.goto (fun _ => 2)))
        (.pop 1 (fun memory _ => memory)
          (.push 15 savedBit (.push 15 (fun _ => true)
            (.push 7 savedBit (.push 7 (fun _ => false)
              (.push 7 (fun _ => false) (.push 7 (fun _ => false) (.goto (fun _ => 1)))))))))))
  else if label = 2 then
    .pop 7 captureFlag
      (.branch savedFlag
        (.goto (fun memory => if positive memory then 4 else 3))
        (.pop 7 captureBit (.push 1 savedBit (.goto (fun _ => 2)))))
  else .halt

def slots (left scratch target : List Bool) (background : Slot → List Bool) : Slot → List Bool :=
  fun slot => if slot = 1 then left else if slot = 7 then scratch else if slot = 15 then target else background slot

def state {C : Type*} (label : Option Label) (memory : Memory C)
    (left scratch target : List Bool) (background : Slot → List Bool) : State C :=
  ⟨label,memory,slots left scratch target background⟩

theorem slots_left (left scratch target : List Bool) (background : Slot → List Bool) :
    slots left scratch target background 1 = left := rfl

theorem slots_scratch (left scratch target : List Bool) (background : Slot → List Bool) :
    slots left scratch target background 7 = scratch := rfl

theorem slots_target (left scratch target : List Bool) (background : Slot → List Bool) :
    slots left scratch target background 15 = target := rfl

theorem slots_frame (left scratch target : List Bool) (background : Slot → List Bool)
    (slot : Slot) (notLeft : slot ≠ 1) (notScratch : slot ≠ 7) (notTarget : slot ≠ 15) :
    slots left scratch target background slot = background slot := by
  simp only [slots,notLeft,notScratch,notTarget,ite_false]

theorem update_left (left scratch target replacement : List Bool) (background : Slot → List Bool) :
    Function.update (slots left scratch target background) 1 replacement = slots replacement scratch target background := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem update_scratch (left scratch target replacement : List Bool) (background : Slot → List Bool) :
    Function.update (slots left scratch target background) 7 replacement = slots left replacement target background := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem update_target (left scratch target replacement : List Bool) (background : Slot → List Bool) :
    Function.update (slots left scratch target background) 15 replacement = slots left scratch replacement background := by
  funext slot
  fin_cases slot <;> simp [slots]

theorem prepare_step {C : Type*} (context : C) (bit flag mode nextMode : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 0) (context,(bit,flag,mode))
      (false :: nextMode :: left) scratch target background) =
      some (state (some (if nextMode then 1 else 2)) (context,(false,flag,nextMode)) left
        (false :: nextMode :: false :: false :: true :: scratch) (false :: false :: target) background) := by
  cases nextMode <;>
    simp [program,state,TM2.step,TM2.stepAux,captureBit,captureMode,savedBit,positive,
      slots_left,slots_scratch,slots_target,update_left,update_scratch,update_target]

theorem payload_step {C : Type*} (context : C) (bit flag digit : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 1) (context,(bit,flag,true))
      (digit :: false :: left) scratch target background) =
      some (state (some 1) (context,(digit,false,true)) left
        (false :: false :: false :: digit :: scratch) (true :: digit :: target) background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,slots_target,update_left,update_scratch,update_target]

theorem boundary_step {C : Type*} (context : C) (bit flag : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 1) (context,(bit,flag,true))
      (false :: true :: left) scratch target background) =
      some (state (some 2) (context,(false,true,true))
        (false :: true :: left) scratch target background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,update_left]

theorem restore_step {C : Type*} (context : C) (bit flag mode cell : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 2) (context,(bit,flag,mode)) left
      (false :: cell :: scratch) target background) =
      some (state (some 2) (context,(cell,false,mode)) (cell :: left) scratch target background) := by
  simp [program,state,TM2.step,TM2.stepAux,captureBit,captureFlag,savedBit,savedFlag,
    slots_left,slots_scratch,update_left,update_scratch]

theorem sentinel_step {C : Type*} (context : C) (bit flag mode : Bool)
    (left scratch target : List Bool) (background : Slot → List Bool) :
    TM2.step program (state (some 2) (context,(bit,flag,mode)) left (true :: scratch) target background) =
      some (state (some (if mode then 4 else 3)) (context,(bit,true,mode)) left scratch target background) := by
  cases mode <;>
    simp [program,state,TM2.step,TM2.stepAux,captureFlag,savedFlag,positive,slots_scratch,update_scratch]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRSymbolicNaturalExport
