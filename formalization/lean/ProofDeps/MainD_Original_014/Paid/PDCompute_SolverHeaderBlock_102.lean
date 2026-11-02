module

public import Paid.PDCompute_SolverChoiceTrace_101

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem HeaderBlockRun.empty (program : Program) (input : List Cell) (before : State)
    (base n k : ℕ) (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) :
    HeaderBlockRun program input before base n k values before.pc 15 := by
  refine ⟨[before],before,rfl,rfl,by simp,?_,header,hbase,rfl,
    ⟨fun _ _ => rfl,fun _ _ => Iff.rfl⟩,rfl,?_⟩
  · exact time_singleton_le program before
  · intro state member
    have same : state=before := List.mem_singleton.mp member
    subst state
    exact HeaderMemory.refl before base

theorem HeaderBlockRun.weaken {program : Program} {input : List Cell} {before : State}
    {base n k finish cost laterCost : ℕ} {values : ℕ → Cell}
    (run : HeaderBlockRun program input before base n k values finish cost) (bound : cost ≤ laterCost) :
    HeaderBlockRun program input before base n k values finish laterCost := by
  obtain ⟨trace,after,head,last,chain,timeBound,header,hbase,hpc,frame,output,memory⟩:=run
  exact ⟨trace,after,head,last,chain,timeBound.trans bound,header,hbase,hpc,frame,output,memory⟩

theorem HeaderBlockRun.headerCode (commands : List HeaderCommand) (program : Program) (input : List Cell)
    (before : State) (base n k : ℕ) (values next : ℕ → Cell)
    (valid : ∀ command ∈ commands,command.Valid) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (evaluate : headerEval commands values=some next)
    (fetch : FetchesCode program before.pc (headerCode commands)) :
    HeaderBlockRun program input before base n k next (before.pc+(headerCode commands).length)
      (165*(commands.length+1)) :=
  headerCode_trace_memory commands program input before base n k values next valid header hbase evaluate fetch

end PDCompute.Solver
