module

public import Paid.PDCompute_SolverHeaderSequence_027

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute loadSlot storeSlot)

/-- Exact scalar-header footprint, including arbitrary live caller cells
inside the solver's larger workspace. Since all48 header cells are
already live, a scalar write creates no additional live cell. -/
def HeaderMemory (before after : State) (base : ℕ) : Prop :=
  (∀ address, address < base ∨ base+headerWords ≤ address → after.heap address=before.heap address) ∧
    after.live=before.live ∧ after.output=before.output

theorem HeaderMemory.refl (before : State) (base : ℕ) : HeaderMemory before before base :=
  ⟨fun _ _ => rfl,rfl,rfl⟩

theorem HeaderMemory.trans {before middle after : State} {base : ℕ}
    (first : HeaderMemory before middle base) (later : HeaderMemory middle after base) :
    HeaderMemory before after base :=
  ⟨fun address outside => (later.1 address outside).trans (first.1 address outside),
    later.2.1.trans first.2.1,later.2.2.trans first.2.2⟩

theorem HeaderMemory.of_unchanged {before after : State} (base : ℕ)
    (heap : after.heap=before.heap) (live : after.live=before.live) (output : after.output=before.output) :
    HeaderMemory before after base := ⟨fun address _ => congrFun heap address,live,output⟩

theorem HeaderMemory.write {before after : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (target : ℕ) (inside : target < headerWords) (value : Cell)
    (heap : after.heap=Function.update before.heap (base+target) value)
    (live : after.live=insert (base+target) before.live) (output : after.output=before.output) :
    HeaderMemory before after base := by
  refine ⟨?_,?_,output⟩
  · intro address outside
    have different : address ≠ base+target := by rcases outside with left|right <;> omega
    rw [heap]
    exact Function.update_of_ne different _ _
  · rw [live,Finset.insert_eq_of_mem (header.live target inside)]

theorem constantSlot_prefix_memory (input : List Cell) (before after : State) (base target : ℕ) (value : Cell)
    (hbase : before.register .fresh=.natural base) (count : ℕ) (hcount : count < 4)
    (hexec : linearExecute input ((constantSlot target value).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [constantSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

theorem copySlot_prefix_memory (input : List Cell) (before after : State) (base source target : ℕ)
    (hbase : before.register .fresh=.natural base) (hlive : base+source ∈ before.live)
    (count : ℕ) (hcount : count < 6)
    (hexec : linearExecute input ((copySlot source target).take count) before=some after) :
    after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  interval_cases count <;>
    simp [copySlot,loadSlot,storeSlot,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,hbase,hlive] at hexec <;>
    subst after <;> exact ⟨rfl,rfl,rfl⟩

end PDCompute.Solver
