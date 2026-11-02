module
public import RootB236_Controller_DFSDriver_Peak018
public import RootB236_Controller_DFSDriver_Stable019
public import RootB236_Controller_DFSDriver_Full016

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace RootB236.Controller.DFSDriver.Machine
open Turing RootB23.GenericRank PaperProofs.Structure
open PaperProofs.Common.Native.PSTRWordBool PaperProofs.Common.Native.PSTRWordVM
open scoped BigOperators
variable {C : Type*}
variable {q : Nat}
attribute [local irreducible] pushProfile actionProfile nodeProfile

def entryCap (bound cap : Nat) : Nat := bound+cap+1
def localTime (bound cap : Nat) : Nat := 4096*(entryCap bound cap+1)
def peak (C : Type*) (bound cap : Nat) : Nat := entryCap bound cap+pushProfile C*localTime bound cap
def nodeTime (bound cap : Nat) : Nat := 16*localTime bound cap

theorem atom {finish : Statement C} {before final : State C} {steps : Nat}
    (run : Run finish before final steps) (bound cap : Nat)
    (bounded : ∀ slot,(before.stk slot).length≤entryCap bound cap) (time : steps≤localTime bound cap) :
    BoundedRun finish (peak C bound cap) before final steps :=
  (run.bounded _ bounded).mono (Nat.add_le_add_left (Nat.mul_le_mul_left (pushProfile C) time) _)

theorem frame_scale_bound (before : Stack → List Bool) (entry : Nat) (bounded : ∀ slot,(before slot).length≤entry) :
    B23_6.DFSFrame.scale before≤16*entry+1 := by
  change (∑ slot : Stack,(before slot).length)+1≤16*entry+1
  apply Nat.add_le_add_right
  calc
    (∑ slot : Stack,(before slot).length)≤∑ _slot : Stack,entry := Finset.sum_le_sum (fun slot _ => bounded slot)
    _=16*entry := by simp

theorem frame_time_bound (before : Stack → List Bool) (bound cap : Nat)
    (bounded : ∀ slot,(before slot).length≤entryCap bound cap) : 51*B23_6.DFSFrame.scale before≤localTime bound cap := by
  have size:=frame_scale_bound before _ bounded
  have small:=Nat.mul_le_mul_left 51 size
  dsimp only [localTime];omega

theorem scan_fields_bound (bg : Stack → List Bool) (bound limit skip : Nat) (best : CodeBest q) (frame : List Bool)
    (bits current parent : List Bool) (tool k : Nat)
    (bounded : FieldsBound bg bound) (limitBound : limit≤bound) (skipBound : skip≤bound) (bestBound : bestCode best≤bound)
    (widthBound : q≤bound) (bitsBound : bits.length≤bound) (currentBound : current.length≤bound)
    (parentBound : parent.length≤bound) (toolBound : tool≤bound) (cursorBound : k≤bound) :
    FieldsBound (scanBank bg limit skip best frame bits current parent tool k) bound := by
  have data:=data_fields_bound bg bound limit skip best frame bounded limitBound skipBound bestBound widthBound
  intro slot outside
  fin_cases slot
  all_goals first | exact data 0 (by decide) | exact data 1 (by decide) | exact data 2 (by decide) | exact data 9 (by decide) | exact data 10 (by decide) | exact data 14 (by decide) | exact data 15 (by decide) | exact bitsBound | exact currentBound |
    exact unary_length_le toolBound |
    exact unary_length_le cursorBound |
    exact reverse_length_le parentBound |
    exact unary_length_le parentBound | exact False.elim (outside rfl)

theorem first_fields_bound (bg : Stack → List Bool) (bound limit skip : Nat) (best : CodeBest q) (frame : List Bool)
    (eligible remaining : Finset (Fin q)) (bounded : FieldsBound bg bound)
    (limitBound : limit≤bound) (skipBound : skip≤bound) (bestBound : bestCode best≤bound) (widthBound : q≤bound) :
    FieldsBound (firstBank bg limit skip best frame eligible remaining) bound := by
  have data:=data_fields_bound bg bound limit skip best frame bounded limitBound skipBound bestBound widthBound
  intro slot outside
  fin_cases slot
  all_goals first | exact data 0 (by decide) | exact data 1 (by decide) | exact data 2 (by decide) | exact data 9 (by decide) | exact data 10 (by decide) | exact data 14 (by decide) | exact data 15 (by decide) |
    exact mask_length_le _ widthBound |
    exact unary_length_le widthBound | exact False.elim (outside rfl)

theorem updated_fields_bound (bg : Stack → List Bool) (bound limit skip : Nat) (best : CodeBest q) (frame : List Bool)
    (bits current parent : List Bool) (tool k rank : Nat)
    (bounded : FieldsBound bg bound) (limitBound : limit≤bound) (skipBound : skip≤bound) (bestBound : bestCode best≤bound)
    (widthBound : q≤bound) (bitsBound : bits.length≤bound) (currentBound : current.length≤bound)
    (parentBound : parent.length≤bound) (toolBound : tool≤bound) (cursorBound : k≤bound) (rankBound : rank≤bound) :
    FieldsBound (bestInput bg limit skip best frame bits current parent tool k rank) bound := by
  apply restore_fields_bound _ bound (unary rank)
  · exact scan_fields_bound bg bound limit skip best frame bits current parent tool k bounded limitBound skipBound bestBound
      widthBound bitsBound currentBound parentBound toolBound cursorBound
  · simpa only [unary,RankCompare.unary,List.length_replicate] using rankBound

theorem update_code_bound (limit : Nat) (best : CodeBest q) (tool : Fin q) (rank : Nat)
    (oldBound : bestCode best≤limit) (rankBound : rank≤limit) : bestCode (updateCode best tool rank)≤limit :=
  code_scan_bound limit (fun _ => rank) [tool] best (fun _ => rankBound) oldBound

/-- Output stability of the physical merge/park/probe block; no accumulation from earlier calls. -/
theorem merge_bank_bound (slots : Stack → List Bool) (bound limit a skip : Nat)
    (bounded : FieldsBound slots bound) (limitBound : limit≤bound) (skipBound : skip≤bound) :
    FieldsBound (Function.update (Function.update (RankMerge.bank slots limit (RankMerge.merged limit a skip) skip) 9 [])
      15 (unary (RankMerge.merged limit a skip))) bound := by
  have merged : RankMerge.merged limit a skip≤bound := (Nat.min_le_right _ _).trans skipBound
  intro slot outside
  fin_cases slot
  all_goals first | exact bounded _ (by decide) | exact Nat.zero_le bound |
    exact unary_length_le limitBound |
    exact unary_length_le skipBound |
    exact unary_length_le merged | exact False.elim (outside rfl)
theorem best_unmapped_input (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool)
    (bits current parent : List Bool) (tool k rank : Nat) :
    BestUpdate.bank (StackIso.slots badRoles (bestInput bg limit skip best tail bits current parent tool k rank))
      (bestCode best) rank tool (toolCode best) (hasCode best) tail=
      StackIso.slots badRoles (bestInput bg limit skip best tail bits current parent tool k rank) := by
  funext slot;fin_cases slot <;> rfl

theorem best_scale_bound (bg : Stack → List Bool) (limit skip : Nat) (best : CodeBest q) (tail : List Bool)
    (bits current parent : List Bool) (tool k rank entry : Nat)
    (bounded : ∀ slot,(bestInput bg limit skip best tail bits current parent tool k rank slot).length≤entry) :
    BestUpdate.scale (StackIso.slots badRoles (bestInput bg limit skip best tail bits current parent tool k rank))
      (bestCode best) rank tool (toolCode best) (hasCode best) tail≤16*entry+1 := by
  change (∑ slot : Stack,(BestUpdate.bank _ _ _ _ _ _ _ slot).length)+1≤16*entry+1
  rw [best_unmapped_input]
  apply Nat.add_le_add_right
  calc
    (∑ slot : Stack,(StackIso.slots badRoles (bestInput bg limit skip best tail bits current parent tool k rank) slot).length)≤
        ∑ _slot : Stack,entry := Finset.sum_le_sum (fun slot _ => bounded (badRoles.symm slot))
    _=16*entry := by simp
end RootB236.Controller.DFSDriver.Machine

