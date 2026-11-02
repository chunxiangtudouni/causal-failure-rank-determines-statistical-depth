module

public import RootL01_SymbolicSource_PacketUnary_Code_027

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootL01.SymbolicSource.PacketUnary

open Turing
open PaperProofs.Common.Native
open PSTRWordVM PSTRWordBool

variable {C : Type*}

theorem collect_path (caller : Statement C)
    (path : List (L01_3_5_TABLE_NatSerializer019.State (C×Unary.Registers)))
    (before final : L01_3_5_TABLE_NatSerializer019.State (C×Unary.Registers))
    (first : path.head? = some before)
    (chain : path.IsChain (fun a b => TM2.step L01_3_5_TABLE_NatSerializer019.collectProgram a = some b))
    (last : path.getLast? = some final) (active : final.l = some 4) :
    (path.map collectConfiguration).head? = some (collectConfiguration before) ∧
    (path.map collectConfiguration).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
    (path.map collectConfiguration).getLast? = some (collectConfiguration final) := by
  have proper := NativeMulLink.no_early_halt_port L01_3_5_TABLE_NatSerializer019.collectProgram 4 rfl path final chain last active
  have mapped := LabelMap.actual_path_on collectLabel L01_3_5_TABLE_NatSerializer019.collectProgram
    (program caller) path before final first chain last (by
      intro current member point selected
      have notDone : point ≠ 4 := by intro same; subst point; exact proper current member selected
      simp only [collectLabel,notDone,ite_false,program])
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

theorem convert_path (caller : Statement C) (path : List (Unary.State (C×RatInput.Store)))
    (before final : Unary.State (C×RatInput.Store))
    (first : path.head? = some before)
    (chain : path.IsChain (fun a b => TM2.step (Unary.program .halt) a = some b))
    (last : path.getLast? = some final) (active : final.l = some .done) :
    (path.map convertConfiguration).head? = some (convertConfiguration before) ∧
    (path.map convertConfiguration).IsChain (fun a b => TM2.step (program caller) a = some b) ∧
    (path.map convertConfiguration).getLast? = some (convertConfiguration final) := by
  let old := Unary.program (C:=C×RatInput.Store) .halt
  let changed := StoreIso.machine (convertIso C) old
  have changedPath := StoreIso.actual_path_on (convertIso C) old changed path before final first chain last
    (by intro current member point selected; rfl)
  have proper := NativeMulLink.no_early_halt_port changed .done rfl _ _
    changedPath.2.1 changedPath.2.2.1 active
  have mapped := LabelMap.actual_path_on convertLabel changed (program caller) _ _ _
    changedPath.1 changedPath.2.1 changedPath.2.2.1 (by
      intro current member point selected
      have notDone : point ≠ .done := by intro same; subst point; exact proper current member selected
      simp only [convertLabel,notDone,ite_false,program]
      rfl)
  have maps : (path.map (StoreIso.configuration (convertIso C))).map (LabelMap.configuration convertLabel) =
      path.map convertConfiguration := by rw [List.map_map]; rfl
  rw [maps] at mapped
  exact ⟨mapped.1,mapped.2.1,mapped.2.2.1⟩

structure Part (caller : Statement C) (before final : State C) (budget : Nat) where
  trace : List (State C)
  first : trace.head? = some before
  chain : trace.IsChain (fun a b => TM2.step (program caller) a = some b)
  last : trace.getLast? = some final
  count : trace.length ≤ budget

def Part.append {caller : Statement C} {before middle final : State C} {A B : Nat}
    (front : Part caller before middle A) (back : Part caller middle final B) : Part caller before final (A+B) := by
  have shape : middle :: back.trace.tail = back.trace := by
    obtain ⟨rest,same⟩ := List.head?_eq_some_iff.mp back.first
    rw [same]
    rfl
  refine ⟨front.trace ++ back.trace.tail,?_,?_,?_,?_⟩
  · rw [List.head?_append,front.first]
    rfl
  · exact NativeTrace.join_chain _ _ _ front.last front.chain (shape.symm ▸ back.chain)
  · exact (NativeTrace.join_last _ _ _ front.last).trans (shape.symm ▸ back.last)
  · have a := front.count
    have b := back.count
    simp only [List.length_append,List.length_tail]
    omega

end RootL01.SymbolicSource.PacketUnary
