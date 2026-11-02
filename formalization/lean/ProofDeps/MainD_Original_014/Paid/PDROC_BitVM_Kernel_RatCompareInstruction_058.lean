module

public import Paid.PDROC_BitVM_Kernel_RatCompareRun_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RatCompare

open Turing PDROC.BitVM.Native PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def after (logical : PaperProofs.Paid.Computation.State) (comparison : Comparison)
    (target : Register) (x y : Rat) :=
  ({logical with pc := logical.pc+1}).set target (.natural (if comparison.rat x y then 1 else 0))

theorem original_execute (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (comparison : Comparison) (target left right : Register) (x y : Rat)
    (leftRat : logical.register left = .rational x) (rightRat : logical.register right = .rational y) :
    Instruction.execute input (.ratCompare comparison target left right) logical =
      some (after logical comparison target x y) := by
  simp [Instruction.execute,leftRat,rightRat,Cell.rat?,after]

/-- Exact original successful comparison, with all three comparisons and
arbitrary operand/destination aliases. The result comes from the actual
difference, captured flags and four real Bool writes, on the same path. -/
theorem instruction_runs {states : ℕ} (machine : Machine states) (comparison : Comparison) (c d : ℕ)
    (contract : RawOp.NativeContract machine (fun x y => x-y) c d)
    (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (target left right : Register) (x y : Rat) (contents : Stack → List Bool)
    (represented : ∀ reg, contents (registerSlot reg) = encodeCellBits (logical.register reg))
    (leftRat : logical.register left = .rational x) (rightRat : logical.register right = .rational y)
    (empty0 : contents 0 = []) (empty24 : contents 24 = []) :
    ∃ (run : List (State states)) (final : State states),
      Instruction.execute input (.ratCompare comparison target left right) logical =
        some (after logical comparison target x y) ∧
      run.head? = some (before states contents) ∧
      run.IsChain (fun a b => TM2.step (program machine comparison target left right) a = some b) ∧
      run.getLast? = some final ∧ TM2.step (program machine comparison target left right) final = none ∧
      RegistersRepresent (after logical comparison target x y) final ∧
      final.stk 0 = [] ∧ final.stk 24 = [] ∧ final.stk 25 = [] ∧ final.stk 29 = [] ∧
      run.length ≤ budget machine logical target left right x y c d contents ∧
      ∀ role, role ≠ 0 → role ≠ 24 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target →
        final.stk role = contents role := by
  obtain ⟨run,final,head,chain,last,halt,word,work0,work24,work25,work29,time,frame⟩ :=
    runs machine comparison c d contract logical target left right x y contents represented leftRat rightRat empty0 empty24
  refine ⟨run,final,original_execute input logical comparison target left right x y leftRat rightRat,
    head,chain,last,halt,?_,work0,work24,work25,work29,time,frame⟩
  intro reg
  by_cases equal : reg = target
  · subst reg
    simpa only [after,PaperProofs.Paid.Computation.State.set,Function.update_self] using word
  · have bounds := registerSlot_bounds reg
    have outside0 : registerSlot reg ≠ 0 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val = 0 at values
      omega
    have outside24 : registerSlot reg ≠ 24 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val = 24 at values
      omega
    have outside25 : registerSlot reg ≠ 25 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val = 25 at values
      omega
    have outside29 : registerSlot reg ≠ 29 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val = 29 at values
      omega
    rw [frame _ outside0 outside24 outside25 outside29 (fun same => equal (registerSlot_injective same)),represented reg]
    simp only [after,PaperProofs.Paid.Computation.State.set,Function.update_of_ne equal]

end PDROC.BitVM.Kernel.RatCompare
