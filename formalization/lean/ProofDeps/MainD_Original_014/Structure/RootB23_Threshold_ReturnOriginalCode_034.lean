module
public import Structure.RootB23_Threshold_ReturnPairReady_037
public import Structure.RootB23_Threshold_OriginalBridge_Actual_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnOriginal
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006
open PSTRTMSeq005

def rowCap : ℕ := OriginalBridge.cap+6709
attribute [local implicit_reducible] rowCap OriginalBridge.cap
theorem before_le : OriginalBridge.cap≤rowCap := by unfold rowCap;omega
theorem after_le : 6709≤rowCap := by unfold rowCap;omega
def rows (phase : Fin 2) : Machine rowCap :=
  if phase.val=0 then padMachine before_le OriginalBridge.code else padMachine after_le ReturnPairReady.code
def bridgeDispatch (control : Fin (OriginalBridge.cap+1)) : Option (Fin 6710) :=
  if control.val=OriginalBridge.truePort.val then some ReturnPairReady.entryTrue
  else if control.val=OriginalBridge.falsePort.val then some ReturnPairReady.entryFalse else none
def ports (phase : Fin 2) (control : Fin (rowCap+1)) : Option (Fin 2 × Fin (rowCap+1)) :=
  if phase.val=0 then
    if small : control.val<OriginalBridge.cap+1 then
      (bridgeDispatch ⟨control.val,small⟩).map (fun destination=>(1,padLabel after_le destination))
    else none
  else none
def cap : ℕ := totalStates 1 rowCap
attribute [local implicit_reducible] cap
def code : Machine cap := blockMachine rows ports
def finalPort (capped : Bool) : Fin (cap+1) := label (p:=1) (s:=rowCap) 1 (padLabel after_le (ReturnPairReady.exitPort capped))
def truePort : Fin (cap+1) := finalPort true
def falsePort : Fin (cap+1) := finalPort false

theorem rows_start : rows (0 : Fin 2)=padMachine before_le OriginalBridge.code := by
  simp only [rows,Fin.val_zero,ite_true]
theorem rows_after : rows (1 : Fin 2)=padMachine after_le ReturnPairReady.code := by
  simp only [rows,show (1 : Fin 2).val=1 by rfl,Nat.one_ne_zero,ite_false]
theorem ports_after (control : Fin (rowCap+1)) : ports (1 : Fin 2) control=none := by
  simp only [ports,show (1 : Fin 2).val=1 by rfl,Nat.one_ne_zero,ite_false]
theorem observed (capped : Bool) : bridgeDispatch (OriginalBridge.finalPort capped)=some (ReturnPairReady.entry capped) := by
  cases capped with
  | false=>
    change bridgeDispatch OriginalBridge.falsePort=some ReturnPairReady.entryFalse
    have different : OriginalBridge.falsePort.val≠OriginalBridge.truePort.val := by
      intro same
      exact OriginalBridge.distinct_ports (Fin.ext same.symm)
    unfold bridgeDispatch
    rw [ite_eq_right different,ite_eq_left rfl]
  | true=>
    change bridgeDispatch OriginalBridge.truePort=some ReturnPairReady.entryTrue
    unfold bridgeDispatch
    rw [ite_eq_left rfl]
theorem ports_observed (control : Fin (OriginalBridge.cap+1)) (destination : Fin 6710)
    (observed : bridgeDispatch control=some destination) :
    ports (0 : Fin 2) (padLabel before_le control)=some (1,padLabel after_le destination) := by
  dsimp only [ports,padLabel]
  simp only [Fin.val_zero,ite_true,dite_eq_left control.isLt]
  change (bridgeDispatch control).map (fun destination=>(1,padLabel after_le destination))=_
  rw [observed]
  rfl

end RootB23.Threshold.ReturnOriginal
