module

public import Common.PSTR_WordVM_UniqueStoreCode_007
public import Common.PSTR_WordVM_FieldTransport_008

/-! Actual insertion phases of the fixed unique-bank source. They execute
in the SAME UniqueStore.program, using concrete constant role/label maps.
The field-prefix traces are the proved copier's SAME explicit witness.
Whole-record search/upsert, raw entry and native costs remain separate. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Common.Native.PSTRWordVM.UniqueStore

open Turing

abbrev TransportFlags := Bool × CallerFlags

def valueRole : FieldCopy.Stack → Stack := BankCopy.role
def keyRole (point : FieldCopy.Stack) : Stack :=
  if point = 0 then 2 else if point = 1 then 10 else
    if point = 2 then 11 else if point = 3 then 5 else 12

def valueLabels (point : FieldCopy.Label) : Label :=
  if point = 0 then 7 else if point = 1 then 8 else 9

def keyLabels (point : FieldCopy.Label) : Label :=
  if point = 0 then 9 else if point = 1 then 10 else 14

theorem valueRole_injective : Function.Injective valueRole := BankCopy.role_injective
theorem keyRole_injective : Function.Injective keyRole := by decide

theorem value_syntax (caller : Statement) (point : FieldCopy.Label) (notTerminal : point ≠ 2) :
    program caller (valueLabels point) =
      FieldTransport.statement valueRole valueLabels (FieldCopy.program point) := by
  fin_cases point
  · rfl
  · rfl
  · exact (notTerminal rfl).elim

theorem key_syntax (caller : Statement) (point : FieldCopy.Label) (notTerminal : point ≠ 2) :
    program caller (keyLabels point) =
      FieldTransport.statement keyRole keyLabels (FieldCopy.program point) := by
  fin_cases point
  · rfl
  · rfl
  · exact (notTerminal rfl).elim

def valueTrace (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) : List State :=
  (FieldCopy.copyPortTrace memory word suffix target).map
    (FieldTransport.configuration valueRole valueLabels background flags)

def valueStart (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) : State :=
  FieldTransport.configuration valueRole valueLabels background flags
    (FieldCopy.copyStart memory word suffix target)

def valuePort (background : Stack → List Bool) (flags : TransportFlags)
    (word suffix target : List Bool) : State :=
  FieldTransport.configuration valueRole valueLabels background flags
    (FieldCopy.copyPort word suffix target)

theorem valueTrace_head (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (valueTrace background flags memory word suffix target).head? =
      some (valueStart background flags memory word suffix target) := by
  simp only [valueTrace, valueStart, List.head?_map, FieldCopy.copyPortTrace_head, Option.map_some]

theorem valueTrace_last (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (valueTrace background flags memory word suffix target).getLast? =
      some (valuePort background flags word suffix target) := by
  simp only [valueTrace, valuePort, List.getLast?_map, FieldCopy.copyPortTrace_last, Option.map_some]

theorem valueTrace_chain (caller : Statement) (background : Stack → List Bool)
    (flags : TransportFlags) (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (valueTrace background flags memory word suffix target).IsChain
      (fun before after => TM2.step (program caller) before = some after) :=
  FieldTransport.portTrace_chain valueRole valueRole_injective valueLabels (program caller)
    (value_syntax caller) background flags memory word suffix target

theorem valueTrace_length (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (valueTrace background flags memory word suffix target).length = 2 * word.length + 3 := by
  simp only [valueTrace, List.length_map, FieldCopy.copyPortTrace_length]

def keyTrace (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) : List State :=
  (FieldCopy.copyPortTrace memory word suffix target).map
    (FieldTransport.configuration keyRole keyLabels background flags)

def keyStart (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) : State :=
  FieldTransport.configuration keyRole keyLabels background flags
    (FieldCopy.copyStart memory word suffix target)

def keyPort (background : Stack → List Bool) (flags : TransportFlags)
    (word suffix target : List Bool) : State :=
  FieldTransport.configuration keyRole keyLabels background flags
    (FieldCopy.copyPort word suffix target)

theorem keyTrace_head (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (keyTrace background flags memory word suffix target).head? =
      some (keyStart background flags memory word suffix target) := by
  simp only [keyTrace, keyStart, List.head?_map, FieldCopy.copyPortTrace_head, Option.map_some]

theorem keyTrace_last (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (keyTrace background flags memory word suffix target).getLast? =
      some (keyPort background flags word suffix target) := by
  simp only [keyTrace, keyPort, List.getLast?_map, FieldCopy.copyPortTrace_last, Option.map_some]

theorem keyTrace_chain (caller : Statement) (background : Stack → List Bool)
    (flags : TransportFlags) (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (keyTrace background flags memory word suffix target).IsChain
      (fun before after => TM2.step (program caller) before = some after) :=
  FieldTransport.portTrace_chain keyRole keyRole_injective keyLabels (program caller)
    (key_syntax caller) background flags memory word suffix target

def tagged (background : Stack → List Bool) (flags : TransportFlags)
    (word suffix target : List Bool) : State :=
  let before := keyPort background flags word suffix target
  ⟨some 11, before.var, Function.update before.stk 10 (true :: before.stk 10)⟩

theorem tag_edge (caller : Statement) (background : Stack → List Bool)
    (flags : TransportFlags) (word suffix target : List Bool) :
    TM2.step (program caller) (keyPort background flags word suffix target) =
      some (tagged background flags word suffix target) := rfl

def keyTaggedTrace (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) : List State :=
  keyTrace background flags memory word suffix target ++ [tagged background flags word suffix target]

theorem keyTaggedTrace_chain (caller : Statement) (background : Stack → List Bool)
    (flags : TransportFlags) (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (keyTaggedTrace background flags memory word suffix target).IsChain
      (fun before after => TM2.step (program caller) before = some after) := by
  apply PSTRWordBool.NativeTrace.join_chain _ (keyPort background flags word suffix target)
    [tagged background flags word suffix target] (keyTrace_last _ _ _ _ _ _)
    (keyTrace_chain caller _ _ _ _ _ _)
  exact List.isChain_cons_cons.mpr ⟨tag_edge caller _ _ _ _ _, List.isChain_singleton _⟩

theorem keyTaggedTrace_length (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    (keyTaggedTrace background flags memory word suffix target).length = 2 * word.length + 4 := by
  simp only [keyTaggedTrace, keyTrace, List.length_append, List.length_map,
    FieldCopy.copyPortTrace_length, List.length_cons, List.length_nil]

/-- Every listed actual TM2 macro boundary preserves the finite eq bit
and caller flags as a pair, as well as all eleven outside physical stacks.
This is not a claim about intermediate stepAux nodes or native clocks. -/
theorem transported_frames
    (role : FieldCopy.Stack → Stack) (labels : FieldCopy.Label → Label)
    (background : Stack → List Bool) (flags : TransportFlags)
    (memory : FieldCopy.Store) (word suffix target : List Bool) :
    ∀ current ∈ (FieldCopy.copyPortTrace memory word suffix target).map
      (FieldTransport.configuration role labels background flags),
      current.var.2 = flags ∧
      ∀ point, (∀ slot, point ≠ role slot) → current.stk point = background point := by
  intro current present
  obtain ⟨small, _, rfl⟩ := List.mem_map.mp present
  exact ⟨rfl, fun point outside => FieldTransport.slots_frame _ _ _ point outside⟩

theorem valuePort_bank (background : Stack → List Bool) (flags : TransportFlags)
    (word suffix target : List Bool) :
    (valuePort background flags word suffix target).stk 10 = word ++ target := by
  change FieldTransport.slots valueRole background (FieldCopy.copyPort word suffix target).stk
    (valueRole 1) = _
  exact FieldTransport.slots_role valueRole valueRole_injective background
    (FieldCopy.copyPort word suffix target).stk 1

theorem tagged_bank (background : Stack → List Bool) (flags : TransportFlags)
    (word suffix target : List Bool) :
    (tagged background flags word suffix target).stk 10 = true :: (word ++ target) := by
  change true :: FieldTransport.slots keyRole background (FieldCopy.copyPort word suffix target).stk
    (keyRole 1) = _
  exact congrArg (List.cons true) (FieldTransport.slots_role keyRole keyRole_injective background
    (FieldCopy.copyPort word suffix target).stk 1)

end PaperProofs.Common.Native.PSTRWordVM.UniqueStore
