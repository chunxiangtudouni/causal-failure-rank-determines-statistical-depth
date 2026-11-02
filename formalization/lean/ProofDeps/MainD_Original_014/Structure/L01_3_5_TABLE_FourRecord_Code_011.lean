module

public import Structure.L01_3_5_TABLE_RecordNav_Original_008
public import Mathlib.Tactic.DeriveFintype

/-! Fixed four-field reader. Read tool, bad, good, rank through the real
getter and previous-natural cursor; unwind three owned cursor frames.
No field value or width is a program parameter. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2200000

namespace PaperProofs.Common.Native.L01_3_5_TABLE_FourRecord011

open Turing
open PaperProofs.Common.Native.PSTRWordVM
open PaperProofs.Common.Native.PSTRWordBool
open PaperProofs.Common.Native.RationalControllerComputation
open L01_3_5_TABLE_Trace005

inductive Label where
  | get : Fin 4 → PSTRSymbolicNaturalExport.Label → Label
  | skip : Fin 3 → L01_3_5_TABLE_RecordNav003.Label → Label
  | restore : Fin 3 → L01_3_5_TABLE_RecordNav003.Label → Label
  | done
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.get 0 0⟩

abbrev Memory (C : Type*) := PSTRSymbolicNaturalExport.Memory C
abbrev State (C : Type*) := TM2.Cfg PSTRSymbolicNaturalExport.Alphabet Label (Memory C)
abbrev Bank := PSTRSymbolicNaturalExport.Slot → List Bool

def afterGet (index : Fin 4) : Label :=
  if within : index.val < 3 then .skip ⟨index.val,within⟩ 0 else .restore 0 3

def afterRestore (index : Fin 3) : Label :=
  if within : index.val+1 < 3 then .restore ⟨index.val+1,within⟩ 3 else .done

def program {C : Type*} : Label → TM2.Stmt PSTRSymbolicNaturalExport.Alphabet Label (Memory C)
  | .get index label =>
      if label = 3 ∨ label = 4 then .goto (fun _ => afterGet index)
      else LabelMap.statement (Label.get index) (PSTRSymbolicNaturalExport.program label)
  | .skip index label =>
      if label = 2 then .goto (fun _ => .get ⟨index.val+1,by omega⟩ 0)
      else LabelMap.statement (Label.skip index) (L01_3_5_TABLE_RecordNav003.program label)
  | .restore index label =>
      if label = 4 then .goto (fun _ => afterRestore index)
      else LabelMap.statement (Label.restore index) (L01_3_5_TABLE_RecordNav003.program label)
  | .done => .halt

theorem get_code {C : Type*} (index : Fin 4) (label : PSTRSymbolicNaturalExport.Label)
    (notHalt : PSTRSymbolicNaturalExport.program (C := C) label ≠ .halt) :
    program (C := C) (Label.get index label) =
      LabelMap.statement (Label.get index) (PSTRSymbolicNaturalExport.program label) := by
  fin_cases label
  · rfl
  · rfl
  · rfl
  · exact False.elim (notHalt rfl)
  · exact False.elim (notHalt rfl)

theorem skip_code {C : Type*} (index : Fin 3) (label : L01_3_5_TABLE_RecordNav003.Label)
    (notHalt : L01_3_5_TABLE_RecordNav003.program (C := C) label ≠ .halt) :
    program (C := C) (Label.skip index label) =
      LabelMap.statement (Label.skip index) (L01_3_5_TABLE_RecordNav003.program label) := by
  have notTwo : label ≠ 2 := by intro same; subst label; exact notHalt rfl
  simp only [program,notTwo,ite_false]

theorem restore_code {C : Type*} (index : Fin 3) (label : L01_3_5_TABLE_RecordNav003.Label)
    (notHalt : L01_3_5_TABLE_RecordNav003.program (C := C) label ≠ .halt) :
    program (C := C) (Label.restore index label) =
      LabelMap.statement (Label.restore index) (L01_3_5_TABLE_RecordNav003.program label) := by
  have notFour : label ≠ 4 := by intro same; subst label; exact notHalt rfl
  simp only [program,notFour,ite_false]

theorem get_lift {C : Type*} (index : Fin 4) (path : List (PSTRSymbolicNaturalExport.State C))
    (final : PSTRSymbolicNaturalExport.State C)
    (chain : path.IsChain (fun before after => TM2.step PSTRSymbolicNaturalExport.program before = some after))
    (last : path.getLast? = some final) (active : final.l ≠ none) :
    (path.map (LabelMap.configuration (Label.get index))).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply LabelMap.chain_configuration_on (Label.get index) PSTRSymbolicNaturalExport.program program path chain
  intro current present label position
  exact get_code index label (proper_not_halt PSTRSymbolicNaturalExport.program path final
    chain last active current present label position)

theorem skip_lift {C : Type*} (index : Fin 3) (path : List (L01_3_5_TABLE_RecordNav003.State C))
    (final : L01_3_5_TABLE_RecordNav003.State C)
    (chain : path.IsChain (fun before after => TM2.step L01_3_5_TABLE_RecordNav003.program before = some after))
    (last : path.getLast? = some final) (active : final.l ≠ none) :
    (path.map (LabelMap.configuration (Label.skip index))).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply LabelMap.chain_configuration_on (Label.skip index) L01_3_5_TABLE_RecordNav003.program program path chain
  intro current present label position
  exact skip_code index label (proper_not_halt L01_3_5_TABLE_RecordNav003.program path final
    chain last active current present label position)

theorem restore_lift {C : Type*} (index : Fin 3) (path : List (L01_3_5_TABLE_RecordNav003.State C))
    (final : L01_3_5_TABLE_RecordNav003.State C)
    (chain : path.IsChain (fun before after => TM2.step L01_3_5_TABLE_RecordNav003.program before = some after))
    (last : path.getLast? = some final) (active : final.l ≠ none) :
    (path.map (LabelMap.configuration (Label.restore index))).IsChain
      (fun before after => TM2.step program before = some after) := by
  apply LabelMap.chain_configuration_on (Label.restore index) L01_3_5_TABLE_RecordNav003.program program path chain
  intro current present label position
  exact restore_code index label (proper_not_halt L01_3_5_TABLE_RecordNav003.program path final
    chain last active current present label position)

def packet (value : Nat) : List Bool :=
  PSTRTMRawNat010.leftBlocks (PSTRTMNatValue017.rawPayload value) ++ [false,false]

def readBank (value : Nat) (bank : Bank) : Bank :=
  Function.update bank 15 (packet value ++ bank 15)

def skipBank (digits tail : List Bool) (bank : Bank) : Bank :=
  Function.update (Function.update bank 1 (false :: true :: tail)) 6
    (PSTRSymbolicNaturalExport.backups (L01_3_5_TABLE_RecordNav003.skipped digits).reverse ++ true :: bank 6)

def restoreBank (cells scratch : List Bool) (bank : Bank) : Bank :=
  Function.update (Function.update bank 1 (cells.reverse ++ bank 1)) 6 scratch

theorem get_return_step {C : Type*} (index : Fin 4) (memory : Memory C) (bank : Bank) :
    TM2.step program (⟨some (.get index 4),memory,bank⟩ : State C) =
      some ⟨some (afterGet index),memory,bank⟩ := rfl

theorem skip_return_step {C : Type*} (index : Fin 3) (memory : Memory C) (bank : Bank) :
    TM2.step program (⟨some (.skip index 2),memory,bank⟩ : State C) =
      some ⟨some (.get ⟨index.val+1,by omega⟩ 0),memory,bank⟩ := rfl

theorem restore_return_step {C : Type*} (index : Fin 3) (memory : Memory C) (bank : Bank) :
    TM2.step program (⟨some (.restore index 4),memory,bank⟩ : State C) =
      some ⟨some (afterRestore index),memory,bank⟩ := rfl

end PaperProofs.Common.Native.L01_3_5_TABLE_FourRecord011
