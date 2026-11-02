module

public import RootL01_SymbolicSource_PacketUnary_Links_028

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.PacketUnary

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool RationalControllerComputation

variable {C : Type*}

def entryBank (frame : Bank) (value : Nat) (tail : List Bool) : Bank :=
  fun slot => if slot=15 then L01_3_5_TABLE_FourRecord011.packet value++tail else
    if slot=3 ∨ slot=5 ∨ slot=6 then [] else frame slot

def entry (frame : Bank) (context : C) (registers : Unary.Registers) (rat : RatInput.Store)
    (value : Nat) (tail : List Bool) : State C :=
  ⟨some (.collect 0),((context,registers),rat),entryBank frame value tail⟩

theorem collect_entry (frame : Bank) (context : C) (registers : Unary.Registers) (rat : RatInput.Store)
    (value : Nat) (tail : List Bool) :
    collectConfiguration (L01_3_5_TABLE_NatSerializer019.collectEntry (entryBank frame value tail)
      (context,registers) rat value tail) = entry frame context registers rat value tail := by
  unfold collectConfiguration LabelMap.configuration L01_3_5_TABLE_NatSerializer019.collectEntry
    RatInput.state entry collectLabel
  simp only [Option.map_some,ite_false,show (0 : Collector) ≠ 4 from by decide]
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem seam (frame : Bank) (value : Nat) (tail : List Bool)
    (before : L01_3_5_TABLE_NatSerializer019.State (C×Unary.Registers))
    (active : before.l=some 4)
    (contents : before.stk=Function.update (entryBank frame value tail) 3 (PSTRTMNatValue017.rawPayload value).reverse) :
    convertConfiguration (Unary.entry (entryBank frame value tail) (before.var.1.1,before.var.2)
      before.var.1.2 (PSTRTMNatValue017.rawPayload value).reverse 0) = collectConfiguration before := by
  rcases before with ⟨position,memory,bank⟩
  change position=some 4 at active
  change bank=Function.update (entryBank frame value tail) 3 (PSTRTMNatValue017.rawPayload value).reverse at contents
  subst position
  subst bank
  unfold convertConfiguration collectConfiguration LabelMap.configuration StoreIso.configuration
    Unary.entry Unary.state collectLabel convertLabel convertIso
  simp only [Option.map_some,ite_true,ite_false,reduceCtorEq]
  congr 1
  funext slot
  fin_cases slot <;> rfl

theorem final_bank (frame : Bank) (context : C) (rat : RatInput.Store) (value : Nat) (tail : List Bool) :
    (convertConfiguration (Unary.final (entryBank frame value tail) (context,rat)
      (PSTRTMNatValue017.rawPayload value).reverse 0)).stk =
        Function.update (entryBank frame value tail) 5 (Unary.unary value) := by
  change Unary.cells (entryBank frame value tail) []
    (Unary.unary (Unary.evaluate (PSTRTMNatValue017.rawPayload value).reverse 0)) [] = _
  rw [Unary.evaluate_canonical]
  funext slot
  fin_cases slot <;> rfl

def time (value : Nat) : Nat := 3*(PSTRTMNatValue017.rawPayload value).length+7+
  Unary.time (PSTRTMNatValue017.rawPayload value).reverse 0

theorem actual (caller : Statement C) (frame : Bank) (context : C) (registers : Unary.Registers)
    (rat : RatInput.Store) (value : Nat) (tail : List Bool) :
    ∃ (trace : List (State C)) (final : State C),
      trace.head?=some (entry frame context registers rat value tail) ∧
      trace.IsChain (fun a b => TM2.step (program caller) a=some b) ∧ trace.getLast?=some final ∧
      final.l=some .done ∧ final.var.1.1=context ∧
      final.stk=Function.update (entryBank frame value tail) 5 (Unary.unary value) ∧
      trace.length ≤ time value := by
  let bank := entryBank frame value tail
  obtain ⟨front,parsed,first,chain,last,active,contexts,contents,count,_bounds⟩ :=
    L01_3_5_TABLE_NatSerializer019.actual_collect_natural bank (context,registers) rat value tail
  have entryContents : (L01_3_5_TABLE_NatSerializer019.collectEntry bank (context,registers) rat value tail).stk=bank := by
    funext slot
    fin_cases slot <;> rfl
  have parsedContents : parsed.stk=Function.update bank 3 (PSTRTMNatValue017.rawPayload value).reverse := by
    rw [entryContents] at contents
    exact contents
  have frontPath := collect_path caller front _ parsed first chain last active
  let parsedState := collectConfiguration parsed
  let start : Part caller (entry frame context registers rat value tail) parsedState
      (3*(PSTRTMNatValue017.rawPayload value).length+7) :=
    ⟨front.map collectConfiguration,frontPath.1.trans (congrArg some (collect_entry frame context registers rat value tail)),
      frontPath.2.1,frontPath.2.2,by simpa only [List.length_map] using count.le⟩
  obtain ⟨back⟩ := Unary.actual (.halt : Unary.Statement (C×RatInput.Store)) bank
    (parsed.var.1.1,parsed.var.2) parsed.var.1.2 (PSTRTMNatValue017.rawPayload value).reverse 0
  have backPath := convert_path caller back.trace _ _ back.first back.chain back.last rfl
  let finish := convertConfiguration (Unary.final bank (parsed.var.1.1,parsed.var.2)
    (PSTRTMNatValue017.rawPayload value).reverse 0)
  let rest : Part caller parsedState finish (Unary.time (PSTRTMNatValue017.rawPayload value).reverse 0) :=
    ⟨back.trace.map convertConfiguration,
      backPath.1.trans (congrArg some (seam frame value tail parsed active parsedContents)),
      backPath.2.1,backPath.2.2,by simpa only [List.length_map] using back.count⟩
  let full := start.append rest
  refine ⟨full.trace,finish,full.first,full.chain,full.last,?_,?_,?_,full.count⟩
  · rfl
  · change parsed.var.1.1=context
    exact congrArg Prod.fst contexts
  · exact final_bank frame parsed.var.1.1 parsed.var.2 value tail

end RootL01.SymbolicSource.PacketUnary
