module

public import Paid.RootD27Core_RetainedLayout_035

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)

/-- Real setup for either retained-table buffer. The returned source
pointer/length are physically saved in reserved core cells46/47. N/K
are read from original prepared heap0/1; the actual solver fresh base
is carried. Only static buffer choice and return PC occur in code. -/
def retainedArgumentsCode (upper : Bool) (returnPC : ℕ) : List Instruction :=
  [.constant .total (.natural 46),.store .total .address,
   .constant .total (.natural 47),.store .total .index,
   .constant .address (.natural 0),.load .total .address,
   .constant .flag (.natural 1),.natOp .add .total .total .flag,
   .constant .address (.natural 1),.load .value .address,
   .natOp .add .value .value .flag,.natOp .multiply .total .total .value,
   .constant .value (.natural (if upper then 70 else 62)),.natOp .multiply .total .total .value,
   .natOp .add .fresh .fresh .total,.constant .address (.natural 46),.load .address .address,
   .constant .value (.natural 47),.load .index .value,.constant .old (.natural returnPC)]

def retainedArgumentsResult (before : State) (base n k source count returnPC : ℕ) (upper : Bool) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update before.register .total
        (.natural ((if upper then 70 else 62)*PDCompute.Solver.entryCount n k)))
        .flag (.natural 1)) .value (.natural 47))
        .fresh (.natural (retainedTableBase base n k upper))) .address (.natural source)) .index (.natural count))
        .old (.natural returnPC)
    heap:=Function.update (Function.update before.heap 46 (.natural source)) 47 (.natural count)
    live:=insert 47 (insert 46 before.live)
    pc:=before.pc+20}

theorem retainedArguments_length (upper : Bool) (returnPC : ℕ) :
    (retainedArgumentsCode upper returnPC).length=20 := rfl

theorem retainedArguments_straight (upper : Bool) (returnPC : ℕ) :
    StraightCode (retainedArgumentsCode upper returnPC) := by
  simp [StraightCode,retainedArgumentsCode,StraightInstruction]

theorem retainedArguments_execute (input : List Cell) (before : State) (base n k source count returnPC : ℕ) (upper : Bool)
    (fresh : before.register .fresh=.natural base) (address : before.register .address=.natural source)
    (index : before.register .index=.natural count) (nLive : 0∈before.live) (kLive : 1∈before.live)
    (nValue : before.heap 0=.natural n) (kValue : before.heap 1=.natural k) :
    linearExecute input (retainedArgumentsCode upper returnPC) before=
      some (retainedArgumentsResult before base n k source count returnPC upper) := by
  cases upper <;>
    simp [retainedArgumentsCode,retainedArgumentsResult,retainedTableBase,PDCompute.Solver.entryCount,
      linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,fresh,address,index,nLive,kLive,nValue,kValue,
      Nat.add_assoc,Nat.mul_comm]
  all_goals
    funext register
    cases register <;> simp

theorem retainedArguments_prefix_memory (input : List Cell) (before after : State)
    (base n k source count returnPC stepsTaken : ℕ) (upper : Bool)
    (fresh : before.register .fresh=.natural base) (address : before.register .address=.natural source)
    (index : before.register .index=.natural count) (nLive : 0∈before.live) (kLive : 1∈before.live)
    (nValue : before.heap 0=.natural n) (kValue : before.heap 1=.natural k)
    (bound : stepsTaken≤20)
    (actual : linearExecute input ((retainedArgumentsCode upper returnPC).take stepsTaken) before=some after) :
    RegionMemory before after {46,47} := by
  interval_cases stepsTaken <;>
    simp [retainedArgumentsCode,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      fresh,address,index,nLive,kLive,nValue,kValue] at actual <;> subst after
  all_goals
    refine ⟨?_,?_,?_,rfl⟩
    · intro query outside
      have q46 : query≠46:=by intro same;subst query;simp at outside
      have q47 : query≠47:=by intro same;subst query;simp at outside
      simp_all
    · intro query member
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at member ⊢
      tauto
    · first
      | exact Finset.Subset.refl _
      | exact Finset.subset_insert _ _
      | exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)

theorem retainedArguments_actual (program : Program) (input : List Cell) (before : State)
    (base n k source count returnPC : ℕ) (upper : Bool)
    (fresh : before.register .fresh=.natural base) (address : before.register .address=.natural source)
    (index : before.register .index=.natural count) (nLive : 0∈before.live) (kLive : 1∈before.live)
    (nValue : before.heap 0=.natural n) (kValue : before.heap 1=.natural k)
    (fetched : FetchesCode program before.pc (retainedArgumentsCode upper returnPC)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (retainedArgumentsResult before base n k source count returnPC upper) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤315 ∧
      (∀ state∈trace,RegionMemory before state {46,47}) := by
  have executed:=retainedArguments_execute input before base n k source count returnPC upper
    fresh address index nLive kLive nValue kValue
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input _
    (retainedArguments_straight upper returnPC) before _ fetched executed
  refine ⟨trace,head,last,chain,cost,?_⟩
  intro state member
  have split:=List.dropLast_append_getLast? (retainedArgumentsResult before base n k source count returnPC upper)
    (by rw [last];simp)
  rw [←split] at member
  rcases List.mem_append.mp member with proper|terminal
  · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
    exact retainedArguments_prefix_memory input before state base n k source count returnPC stepsTaken upper
      fresh address index nLive kLive nValue kValue (by simpa only [retainedArguments_length] using bound.le) actual
  · exact retainedArguments_prefix_memory input before state base n k source count returnPC 20 upper
      fresh address index nLive kLive nValue kValue (le_refl _) (by
        have same : state=retainedArgumentsResult before base n k source count returnPC upper:=List.mem_singleton.mp terminal
        subst state
        rw [←retainedArguments_length upper returnPC,List.take_length]
        exact executed)

end RootD27.Core
