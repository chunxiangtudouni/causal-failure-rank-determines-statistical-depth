module
public import PaperProofs.Common.PSTR_TM_PadTrace_035
public import PaperProofs.Common.PSTR_TM_MulRewind_085

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandCode095
open PaperProofs.Common.Native.RationalControllerComputation

def padLabel (savedA : Bool) (q : Fin 41) : Fin 112 :=
  ⟨11+41*savedA.toNat+q.val,by have hq := q.isLt; have ha := Bool.toNat_le savedA; omega⟩
def rewindLabel (q : Fin 4) : Fin 112 := ⟨108+q.val,by have hq := q.isLt; omega⟩
def liftPad (savedA : Bool) (old : MachineState 40) : MachineState 111 := ⟨padLabel savedA old.q,old.Tape⟩
def liftRewind (old : MachineState 3) : MachineState 111 := ⟨rewindLabel old.q,old.Tape⟩

/-- ONE fixed112-label original operand-column to resident multiplication
tuple expander. It ACTUALLY reads A into finite control, marks its pair10,
calls the existing real two-cell prefix-shifter034/035, writes C=0/flag1,
restores the saved A/flag and advances across retained B. EOF really calls
the existing pair rewind085. No input width, duplicated operands, padding,
output answer or head-reset oracle. Correctness/cost are proved separately.
The existing prefix is physically shifted two cells LEFT per input tuple;
therefore the original blank-left tape is required, no archive frame claim. -/
def expandMachine : Machine 111 := fun q symbol =>
  if h0 : q.val<11 then
    if q.val=0 then some (⟨1+symbol.toNat,by have h := Bool.toNat_le symbol; omega⟩,.move .right)
    else if h1 : q.val<3 then
      if symbol then some (⟨q.val+2,by omega⟩,.move .left) else some (108,.move .left)
    else if h2 : q.val<5 then some (⟨q.val+2,by omega⟩,.write true)
    else if h3 : q.val<7 then some (⟨q.val+2,by omega⟩,.move .right)
    else if h4 : q.val<9 then some (⟨q.val+2,by omega⟩,.write false)
    else some (padLabel (decide (q.val=10)) 0,.move .left)
  else if h1 : q.val<52 then
    if q.val=51 then some (93,.write false)
    else (PSTRTMPadInsert034.padMachine ⟨q.val-11,by omega⟩ symbol).map
      (fun (next,statement) => (padLabel false next,statement))
  else if h2 : q.val<93 then
    if q.val=92 then some (94,.write false)
    else (PSTRTMPadInsert034.padMachine ⟨q.val-52,by omega⟩ symbol).map
      (fun (next,statement) => (padLabel true next,statement))
  else if h3 : q.val<108 then
    if h4 : q.val<95 then some (⟨q.val+2,by omega⟩,.move .right)
    else if h5 : q.val<97 then some (⟨q.val+2,by omega⟩,.write true)
    else if h6 : q.val<99 then some (⟨q.val+2,by omega⟩,.move .right)
    else if h7 : q.val<101 then some (⟨q.val+2,by omega⟩,.write (decide (q.val=100)))
    else if h8 : q.val<103 then some (⟨q.val+2,by omega⟩,.move .right)
    else if q.val<105 then some (105,.write true)
    else if q.val=105 then some (106,.move .right)
    else if q.val=106 then some (107,.move .right)
    else some (0,.move .right)
  else (PSTRTMMulRewind085.rewindMachine ⟨q.val-108,by have hq := q.isLt; omega⟩ symbol).map
    (fun (next,statement) => (rewindLabel next,statement))

def state (q : Fin 112) (left right : List Bool) : MachineState 111 := ⟨q,Turing.Tape.mk₂ left right⟩
def triples (pairs : List (Bool×Bool)) : List PSTRTMMulPassCode079.Triple := pairs.map (fun (a,b) => (false,a,b))

theorem expand_halt (left right : List Bool) : Turing.TM0.step expandMachine (state 111 left right)=none := by
  simp [Turing.TM0.step,expandMachine,state,PSTRTMMulRewind085.rewindMachine]

end PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulExpandCode095
