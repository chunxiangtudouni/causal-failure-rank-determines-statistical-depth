module

public import Paid.PDROC_BitVM_Log_TM2_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Literal self-delimiting-header scanner. Width is counted by Boolean ticks
on stack 1, not by a Nat in sigma. Stack 2 archives every consumed input bit.
This is not yet address comparison, heap lookup or an interpreter. -/

namespace PDROC.BitVM.Log.Header

open Turing

abbrev Stack := TwoStack.Stack
abbrev Label := Fin 4
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Option Bool
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def slots (input ticks archive : List Bool) : Stack → List Bool :=
  TwoStack.stackContents 0 1 input ticks (fun _ => archive)

def state (label : Option Label) (store : Store) (input ticks archive : List Bool) : State :=
  ⟨label, store, slots input ticks archive⟩

def readHeader : Statement :=
  .pop 0 (fun _ symbol => symbol)
    (.branch Option.isSome
      (.branch (fun symbol => symbol.getD false)
        (.push 1 (fun _ => true) (.push 2 (fun _ => true) (.goto (fun _ => 0))))
        (.push 2 (fun _ => false) (.goto (fun _ => 1))))
      (.goto (fun _ => 3)))

def readPayload : Statement :=
  .pop 1 (fun _ symbol => symbol)
    (.branch Option.isSome
      (.pop 0 (fun _ symbol => symbol)
        (.branch Option.isSome
          (.push 2 (fun symbol => symbol.getD false) (.goto (fun _ => 1)))
          (.goto (fun _ => 3))))
      (.goto (fun _ => 2)))

def program (label : Label) : Statement :=
  if label = 0 then readHeader else if label = 1 then readPayload else .halt

theorem update_input (input ticks archive replacement : List Bool) :
    Function.update (slots input ticks archive) 0 replacement = slots replacement ticks archive :=
  TwoStack.update_source 0 1 input ticks replacement (fun _ => archive)

theorem update_ticks (input ticks archive replacement : List Bool) :
    Function.update (slots input ticks archive) 1 replacement = slots input replacement archive :=
  TwoStack.update_target 0 1 (by decide) input ticks replacement (fun _ => archive)

theorem update_archive (input ticks archive replacement : List Bool) :
    Function.update (slots input ticks archive) 2 replacement = slots input ticks replacement := by
  funext stack
  fin_cases stack <;> simp [slots, TwoStack.stackContents]

theorem header_true (input ticks archive : List Bool) (store : Store) :
    TM2.step program (state (some 0) store (true :: input) ticks archive) =
      some (state (some 0) (some true) input (true :: ticks) (true :: archive)) := by
  change (some ⟨some 0, some true,
    Function.update (Function.update (Function.update (slots (true :: input) ticks archive)
      0 input) 1 (true :: ticks)) 2 (true :: archive)⟩ : Option State) = _
  rw [update_input, update_ticks, update_archive]
  rfl

theorem header_false (input ticks archive : List Bool) (store : Store) :
    TM2.step program (state (some 0) store (false :: input) ticks archive) =
      some (state (some 1) (some false) input ticks (false :: archive)) := by
  change (some ⟨some 1, some false,
    Function.update (Function.update (slots (false :: input) ticks archive)
      0 input) 2 (false :: archive)⟩ : Option State) = _
  rw [update_input, update_archive]
  rfl

theorem header_eof (ticks archive : List Bool) (store : Store) :
    TM2.step program (state (some 0) store [] ticks archive) =
      some (state (some 3) none [] ticks archive) := by
  change (some ⟨some 3, none,
    Function.update (slots [] ticks archive) 0 []⟩ : Option State) = _
  rw [update_input]
  rfl

theorem payload_bit (bit : Bool) (input ticks archive : List Bool) (store : Store) :
    TM2.step program (state (some 1) store (bit :: input) (true :: ticks) archive) =
      some (state (some 1) (some bit) input ticks (bit :: archive)) := by
  change (some ⟨some 1, some bit,
    Function.update (Function.update (Function.update (slots (bit :: input) (true :: ticks) archive)
      1 ticks) 0 input) 2 (bit :: archive)⟩ : Option State) = _
  rw [update_ticks, update_input, update_archive]
  rfl

theorem payload_done (input archive : List Bool) (store : Store) :
    TM2.step program (state (some 1) store input [] archive) =
      some (state (some 2) none input [] archive) := by
  change (some ⟨some 2, none,
    Function.update (slots input [] archive) 1 []⟩ : Option State) = _
  rw [update_ticks]
  rfl

theorem payload_eof (ticks archive : List Bool) (store : Store) :
    TM2.step program (state (some 1) store [] (true :: ticks) archive) =
      some (state (some 3) none [] ticks archive) := by
  change (some ⟨some 3, none,
    Function.update (Function.update (slots [] (true :: ticks) archive) 1 ticks) 0 []⟩ : Option State) = _
  rw [update_ticks, update_input]
  rfl

theorem return_halt (input archive : List Bool) :
    TM2.step program (state (some 2) none input [] archive) =
      some (state none none input [] archive) := rfl

theorem halted (input archive : List Bool) :
    TM2.step program (state none none input [] archive) = none := rfl

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label <;> simp [program, readHeader, readPayload, TM2.SupportsStmt]

end PDROC.BitVM.Log.Header
