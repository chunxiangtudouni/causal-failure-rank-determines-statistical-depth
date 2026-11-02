module
public import Common.PSTR_TM_MulAppendTrace_087
public import Common.PSTR_TM_MulHalfTrace_084

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopCode088
open PaperProofs.Common.Native.RationalControllerComputation

def halfLabel (q : Fin 34) : Fin 264 := ⟨2+q.val,by have h := q.isLt; omega⟩
def appendLabel (mode : Bool) (q : Fin 18) : Fin 264 :=
  ⟨36+18*mode.toNat+q.val,by have h := q.isLt; have hm := Bool.toNat_le mode; omega⟩
def passLabel (q : Fin 192) : Fin 264 := ⟨72+q.val,by have h := q.isLt; omega⟩
def liftHalf (old : MachineState 33) : MachineState 263 := ⟨halfLabel old.q,old.Tape⟩
def liftAppend (mode : Bool) (old : MachineState 17) : MachineState 263 := ⟨appendLabel mode old.q,old.Tape⟩
def liftPass (old : MachineState 191) : MachineState 263 := ⟨passLabel old.q,old.Tape⟩

/-- ONE fixed264-label binary multiplication accumulator loop.
ACTUAL halver HALT control selects zero-stop or the OLD multiplier bit;
both constant copies of the real high-zero allocator are in the code.
The pass doubles A/adds bit*A to C; B has REALLY been halved. No numerical
multiplier counter or supplied parity/termination/width/answer is input.
Complete correctness/cost and original input/output wrappers remain owed. -/
def loopMachine : Machine 263 := fun q symbol =>
  if h0 : q.val<2 then
    if q.val=0 then some (1,.move .right)
      else if symbol then some (0,.move .right) else some (2,.move .left)
  else if h1 : q.val<36 then
    if q.val=33 then some (36,.write symbol)
    else if q.val=34 ∨ q.val=35 then some (54,.write symbol)
    else (PSTRTMMulHalfCode082.halfMachine ⟨q.val-2,by omega⟩ symbol).map
      (fun (next,statement) => (halfLabel next,statement))
  else if h2 : q.val<54 then
    if q.val=53 then some (72,.write symbol)
    else (PSTRTMMulAppendCode086.appendMachine ⟨q.val-36,by omega⟩ symbol).map
      (fun (next,statement) => (appendLabel false next,statement))
  else if h3 : q.val<72 then
    if q.val=71 then some (76,.write symbol)
    else (PSTRTMMulAppendCode086.appendMachine ⟨q.val-54,by omega⟩ symbol).map
      (fun (next,statement) => (appendLabel true next,statement))
  else if q.val=256 ∨ q.val=260 then some (2,.write symbol)
  else (PSTRTMMulPassCode079.passMachine ⟨q.val-72,by have hq := q.isLt; omega⟩ symbol).map
    (fun (next,statement) => (passLabel next,statement))

def state (q : Fin 264) (left right : List Bool) : MachineState 263 := ⟨q,Turing.Tape.mk₂ left right⟩

theorem loop_halt (left right : List Bool) : Turing.TM0.step loopMachine (state 32 left right)=none := by
  simp [Turing.TM0.step,loopMachine,state,PSTRTMMulHalfCode082.halfMachine]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulLoopCode088
