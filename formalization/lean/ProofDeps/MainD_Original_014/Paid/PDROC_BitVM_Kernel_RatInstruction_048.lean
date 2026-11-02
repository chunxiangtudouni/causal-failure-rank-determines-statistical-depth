module

public import Paid.PDROC_BitVM_Kernel_RawRun_046
public import Paid.PDROC_BitVM_Kernel_RawDiv_042

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawInstruction

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def after (logical : PaperProofs.Paid.Computation.State) (target : Register) (result : Rat) :=
  ({logical with pc:=logical.pc+1}).set target (.rational result)

def Matches (operation : RatOp) (resultFn : Rat → Rat → Rat) : Prop :=
  ∀ x y result,operation.eval x y=some result → resultFn x y=result

theorem multiply_matches : Matches .multiply (fun x y=>x*y) := by
  intro x y result success
  exact Option.some.inj success

theorem divide_matches : Matches .divide (fun x y=>x/y) := by
  intro x y result success
  by_cases zero : y=0
  · simp [RatOp.eval,zero] at success
  · simpa only [RatOp.eval,ite_eq_right zero,Option.some.injEq] using success

theorem original_execute (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (operation : RatOp) (target left right : Register) (x y result : Rat)
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y)
    (success : operation.eval x y=some result) :
    Instruction.execute input (.ratOp operation target left right) logical=some (after logical target result) := by
  simp [Instruction.execute,leftRat,rightRat,Cell.rat?,success,after]

/-- Exact original successful rational instruction refinement. The source
operation, fixed finite native machine and its uniform correctness theorem
are chosen before inputs. Source success is a proof of the original step,
not an added machine input, target value, tape width or numerical oracle. -/
theorem instruction_runs {states : ℕ} (machine : Machine states) (operation : RatOp)
    (resultFn : Rat → Rat → Rat) (c d : ℕ)
    (contract : RawOp.NativeContract machine resultFn c d) (compatible : Matches operation resultFn)
    (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (target left right : Register) (x y result : Rat) (contents : Stack → List Bool)
    (represented : ∀ reg,contents (registerSlot reg)=encodeCellBits (logical.register reg))
    (leftRat : logical.register left=.rational x) (rightRat : logical.register right=.rational y)
    (success : operation.eval x y=some result) (empty0 : contents 0=[]) (empty24 : contents 24=[]) :
    ∃ (run : List (State states)) (final : State states),
      Instruction.execute input (.ratOp operation target left right) logical=some (after logical target result) ∧
      run.head?=some (before states contents) ∧
      run.IsChain (fun a b=>TM2.step (program machine target left right) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (program machine target left right) final=none ∧
      RegistersRepresent (after logical target result) final ∧
      final.stk 0=[] ∧ final.stk 24=[] ∧ final.stk 25=[] ∧ final.stk 29=[] ∧
      run.length ≤ budget machine logical left right x y c d contents ∧
      ∀ role,role ≠ 0 → role ≠ 24 → role ≠ 25 → role ≠ 29 → role ≠ registerSlot target →
        final.stk role=contents role := by
  obtain ⟨run,final,head,chain,last,halt,word,work0,work24,work25,work29,time,frame⟩ :=
    runs machine resultFn c d contract logical target left right x y contents represented leftRat rightRat empty0 empty24
  have same : resultFn x y=result := compatible x y result success
  rw [same] at word
  refine ⟨run,final,original_execute input logical operation target left right x y result leftRat rightRat success,
    head,chain,last,halt,?_,work0,work24,work25,work29,time,frame⟩
  intro reg
  by_cases equal : reg=target
  · subst reg
    simpa only [after,PaperProofs.Paid.Computation.State.set,Function.update_self] using word
  · have bounds := registerSlot_bounds reg
    have outside0 : registerSlot reg ≠ 0 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val=0 at values
      omega
    have outside24 : registerSlot reg ≠ 24 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val=24 at values
      omega
    have outside25 : registerSlot reg ≠ 25 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val=25 at values
      omega
    have outside29 : registerSlot reg ≠ 29 := by
      intro same
      have values := congrArg Fin.val same
      change (registerSlot reg).val=29 at values
      omega
    rw [frame _ outside0 outside24 outside25 outside29 (fun same=>equal (registerSlot_injective same)),represented reg]
    simp only [after,PaperProofs.Paid.Computation.State.set,Function.update_of_ne equal]

/-- Two original RAW operator machines are genuinely supplied now. Add
and subtract still require their own frozen original machine contracts. -/
theorem actual_multiply : ∃ states c d : ℕ,∃ machine : Machine states,
    0<c ∧ 0<d ∧ RawOp.NativeContract machine (fun x y=>x*y) c d ∧ Matches .multiply (fun x y=>x*y) := by
  obtain ⟨states,c,d,machine,positiveC,positiveD,contract⟩ := RawOp.actual_mul_contract
  exact ⟨states,c,d,machine,positiveC,positiveD,contract,multiply_matches⟩

theorem actual_divide : ∃ states c d : ℕ,∃ machine : Machine states,
    0<c ∧ 0<d ∧ RawOp.NativeContract machine (fun x y=>x/y) c d ∧ Matches .divide (fun x y=>x/y) := by
  obtain ⟨states,c,d,machine,positiveC,positiveD,contract⟩ := RawOp.actual_div_contract
  exact ⟨states,c,d,machine,positiveC,positiveD,contract,divide_matches⟩

end PDROC.BitVM.Kernel.RawInstruction
