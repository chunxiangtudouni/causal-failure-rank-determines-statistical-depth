module

public import Paid.RootD27Core_RetainedArguments_036

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)

/-- The last three actual dense cells precede the returned serialized
table pointer. Read them physically, store the requested core triple,
then recompute the solver base from real prepared heap7. The returned
table pointer/count remain in address/index for real retention copying. -/
def rootStatisticsCode (target : ℕ) : List Instruction :=
  [.constant .total (.natural 3),.natOp .subtract .total .address .total,
   .load .flag .total,.constant .fresh (.natural target),.store .fresh .flag,
   .constant .value (.natural 1),.natOp .add .total .total .value,
   .load .flag .total,.constant .fresh (.natural (target+1)),.store .fresh .flag,
   .natOp .add .total .total .value,.load .flag .total,
   .constant .fresh (.natural (target+2)),.store .fresh .flag,
   .constant .flag (.natural 7),.load .fresh .flag,
   .constant .total (.natural 2),.natOp .multiply .fresh .fresh .total,
   .constant .total (.natural 99),.natOp .add .fresh .fresh .total]

def rootStatisticsResult (before : State) (target menu : ℕ) (observation repairs failure : ℚ) : State :=
  {before with
    register:=Function.update (Function.update (Function.update (Function.update before.register
      .value (.natural 1)) .flag (.natural 7)) .total (.natural 99)) .fresh (.natural (99+2*menu))
    heap:=Function.update (Function.update (Function.update before.heap target (.rational observation))
      (target+1) (.rational repairs)) (target+2) (.rational failure)
    live:=insert (target+2) (insert (target+1) (insert target before.live))
    pc:=before.pc+20}

theorem rootStatistics_length (target : ℕ) : (rootStatisticsCode target).length=20:=rfl

theorem rootStatistics_straight (target : ℕ) : StraightCode (rootStatisticsCode target) := by
  simp [StraightCode,rootStatisticsCode,StraightInstruction]

theorem rootStatistics_execute (input : List Cell) (before : State) (target source menu : ℕ)
    (observation repairs failure : ℚ) (lower : 13≤target) (upper : target+2<46) (sourceBound : 51≤source)
    (address : before.register .address=.natural source)
    (root : HeapList before (source-3) [.rational observation,.rational repairs,.rational failure])
    (menuLive : 7∈before.live) (menuValue : before.heap 7=.natural menu) :
    linearExecute input (rootStatisticsCode target) before=
      some (rootStatisticsResult before target menu observation repairs failure) := by
  have ol:=root.1 0 (by change 0<3;decide)
  have rl:=root.1 1 (by change 1<3;decide)
  have fl:=root.1 2 (by change 2<3;decide)
  have ov:=PDLower.CalibrationCompute.HeapList.value root 0 (by change 0<3;decide)
  have rv:=PDLower.CalibrationCompute.HeapList.value root 1 (by change 1<3;decide)
  have fv:=PDLower.CalibrationCompute.HeapList.value root 2 (by change 2<3;decide)
  simp only [Nat.add_zero,List.getElem_cons_zero,List.getElem_cons_succ] at ol ov rv fv
  have r0 : source-3≠target:=by omega
  have r1 : source-3+1≠target:=by omega
  have r2 : source-3+2≠target:=by omega
  have s1 : source-3+1≠target+1:=by omega
  have s2 : source-3+2≠target+1:=by omega
  have t0 : 7≠target:=by omega
  have t1 : 7≠target+1:=by omega
  have t2 : 7≠target+2:=by omega
  have arithmetic : menu*2+99=99+2*menu:=by omega
  simp [rootStatisticsCode,rootStatisticsResult,linearExecute,Instruction.execute,State.set,
    NatOp.eval,Cell.nat?,address,ol,rl,fl,ov,rv,fv,menuLive,menuValue,
    r1,r2,s2,t0,t1,t2,arithmetic,Nat.add_assoc]
  all_goals
    funext register
    cases register <;> simp

end RootD27.Core
