module

public import Paid.PDROC_BitVM_Codec_NatWriter_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.NatWriter.Global

open Turing PaperProofs.Common.Native.RationalControllerComputation
open PDROC.BitVM.Native

abbrev Stack := Fin 32
abbrev Alphabet (_ : Stack) := Bool
abbrev State := TM2.Cfg Alphabet NatWriter.Label NatWriter.Store

/-- The target and this finite renaming are fixed before runtime values.
The other six temporary registers and every original register are outside
the machine unless that exact fixed slot was selected as destination. -/
def embedding (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24) :
    NatWriter.Stack ↪ Stack where
  toFun := fun role => if role = 0 then 0 else if role = 1 then 24 else dst
  inj' := by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all

def machine (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24) :
    NatWriter.Label → TM2.Stmt Alphabet NatWriter.Label NatWriter.Store :=
  Lift.machine (embedding dst notRight notLeft) NatWriter.program

def before (contents : Stack → List Bool) (store : Option Bool) : State :=
  ⟨some 0, (store, ()), contents⟩

theorem initial_projection (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24)
    (contents : Stack → List Bool) (store : Option Bool) :
    Lift.cfg (embedding dst notRight notLeft) (before contents store) =
      NatWriter.before (contents 0) (contents 24) (contents dst) store := by
  have slots : Lift.slots (embedding dst notRight notLeft) contents =
      PDROC.BitVM.Log.TwoStack.threeStacks (contents 0) (contents 24) (contents dst) := by
    funext role
    fin_cases role <;> rfl
  change (⟨some 0, (store, ()), Lift.slots (embedding dst notRight notLeft) contents⟩ :
    NatWriter.State) = _
  rw [slots]
  rfl

theorem supports (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24) :
    TM2.Supports (machine dst notRight notLeft) (Finset.univ : Finset NatWriter.Label) :=
  Lift.supports (embedding dst notRight notLeft) NatWriter.program _
    (NatWriter.finite_labels_support NatWriter.program)

/-- One lift of the SAME complete actual local writer path. Arbitrary
inactive global data is retained literally; it is never supplied as empty
workspace. Only the three selected physical lengths pay writer cost. -/
theorem runs (dst : Stack) (notRight : dst ≠ 0) (notLeft : dst ≠ 24)
    (value : ℕ) (contents : Stack → List Bool) (store : Option Bool)
    (representation : ListBlank.mk (contents 0) = ListBlank.mk (encodeNat value)) :
    ∃ (run : List State) (after : State),
      run.head? = some (before contents store) ∧
      run.IsChain (fun a b => TM2.step (machine dst notRight notLeft) a = some b) ∧
      run.getLast? = some after ∧ TM2.step (machine dst notRight notLeft) after = none ∧
      after.stk 0 = [] ∧ after.stk 24 = [] ∧
      after.stk dst = PaperProofs.Paid.Computation.encodeCellBits (.natural value) ∧
      run.length ≤ 32 * ((contents 0).length + (contents 24).length + (contents dst).length + 1) ∧
      ∀ other, other ≠ 0 → other ≠ 24 → other ≠ dst → after.stk other = contents other := by
  obtain ⟨source, originalFinal, head, chain, last, halt, rightEmpty, leftEmpty,
    exactCell, time, _occupied⟩ := NatWriter.runs value (contents 0) (contents 24) (contents dst)
      store representation
  cases source with
  | nil => simp only [List.head?_nil, reduceCtorEq] at head
  | cons start rest =>
    have same : start = NatWriter.before (contents 0) (contents 24) (contents dst) store :=
      Option.some.inj head
    subst start
    obtain ⟨posts, after, length, actual, final, projected, frame⟩ :=
      Lift.path (embedding dst notRight notLeft) NatWriter.program (before contents store)
        (NatWriter.before (contents 0) (contents 24) (contents dst) store) originalFinal rest
        (initial_projection dst notRight notLeft contents store) chain last
    refine ⟨before contents store :: posts, after, rfl, actual, final, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply Lift.halt_project (embedding dst notRight notLeft) NatWriter.program after
      rw [projected]
      exact halt
    · have selected := congrArg (fun state : NatWriter.State => state.stk 0) projected
      exact selected.trans rightEmpty
    · have selected := congrArg (fun state : NatWriter.State => state.stk 1) projected
      exact selected.trans leftEmpty
    · have selected := congrArg (fun state : NatWriter.State => state.stk 2) projected
      exact selected.trans exactCell
    · simp only [List.length_cons, length] at time ⊢
      exact time
    · intro other not0 not24 notDst
      apply frame other
      intro role
      fin_cases role
      · exact not0
      · exact not24
      · exact notDst

end PDROC.BitVM.Codec.NatWriter.Global
