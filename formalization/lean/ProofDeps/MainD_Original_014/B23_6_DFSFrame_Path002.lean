module
public import B23_6_DFSFrame_Code001

/-! Counted executions of the literal source. Every executed label is an
interior; the last active caller label is never executed by the callee. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open Turing
variable {C : Type*}

def Active (before : State C) : Prop := ∃ point,before.l=some point ∧ Interior point

inductive Run : State C → State C → Nat → Prop where
  | refl (before) : Run before before 0
  | cons {before after final : State C} {n : Nat}
      (edge : TM2.step source before=some after) (active : Active before)
      (tail : Run after final n) : Run before final (n+1)

namespace Run
theorem one {before after : State C} (edge : TM2.step source before=some after)
    (active : Active before) : Run before after 1 := .cons edge active (.refl after)

theorem trans {a b c : State C} {n m : Nat} (first : Run a b n) (second : Run b c m) :
    Run a c (n+m) := by
  induction first with
  | refl => simpa only [Nat.zero_add] using second
  | @cons before after final n edge active tail ih =>
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Run.cons edge active (ih second)

theorem witness {before after : State C} {n : Nat} (run : Run before after n) :
    ∃ path : List (State C),path.head?=some before ∧ path.getLast?=some after ∧
      path.IsChain (fun a b => TM2.step source a=some b) ∧ path.length=n+1 ∧
      ∀ current∈path.dropLast,Active current := by
  induction run with
  | refl current => exact ⟨[current],rfl,rfl,List.isChain_singleton _,rfl,by simp⟩
  | @cons before after final n edge active tail ih =>
    obtain ⟨path,first,last,chain,count,proper⟩:=ih
    cases path with
    | nil => simp at first
    | cons start rest =>
      have equal : start=after:=Option.some.inj first
      subst start
      refine ⟨before::after::rest,rfl,?_,List.isChain_cons_cons.mpr ⟨edge,chain⟩,?_,?_⟩
      · simpa only [List.getLast?_cons_cons] using last
      · simp only [List.length_cons] at count ⊢;omega
      · rw [List.dropLast_cons_cons]
        intro current member
        rcases List.mem_cons.mp member with rfl | member
        · exact active
        · exact proper current member
end Run

theorem active_state (point : Label) (memory : Store C) (before : Bank) (proper : Interior point) :
    Active (state point memory before) := ⟨point,rfl,proper⟩

end B23_6.DFSFrame
