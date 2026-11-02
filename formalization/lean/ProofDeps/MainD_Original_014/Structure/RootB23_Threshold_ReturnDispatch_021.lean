module
public import Structure.RootB23_Threshold_ReturnBank_019
public import Structure.RootB23_Threshold_ReturnAnchor_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000
@[expose] public section
namespace RootB23.Threshold.ReturnDispatch
open PaperProofs.Common.Native.RationalControllerComputation Turing PA17TMDivisionCompose006

def falseCode : Machine 72 := PSTRTMSeq005.seqMachine ReturnAnchor.falseCode ReturnBank.code
def trueCode : Machine 109 := PSTRTMSeq005.seqMachine ReturnAnchor.trueCode ReturnBank.code
def rows (phase : Fin 2) : Machine 109 :=
  if phase.val=0 then padMachine (by decide : 72≤109) falseCode else trueCode
def ports (_phase : Fin 2) (_q : Fin 110) : Option (Fin 2×Fin 110) := none
def code : Machine 219 := blockMachine rows ports

def entryFalse : Fin 220 := label (p:=1) (s:=109) (0 : Fin 2) (0 : Fin 110)
def entryTrue : Fin 220 := label (p:=1) (s:=109) (1 : Fin 2) (0 : Fin 110)
def entry (capped : Bool) : Fin 220 := if capped then entryTrue else entryFalse
def exitFalse : Fin 220 := label (p:=1) (s:=109) (0 : Fin 2) (padLabel (by decide : 72≤109) (72 : Fin 73))
def exitTrue : Fin 220 := label (p:=1) (s:=109) (1 : Fin 2) (109 : Fin 110)
def exitPort (capped : Bool) : Fin 220 := if capped then exitTrue else exitFalse

/-- The two EXACT nested control labels of Window029. prefixCap is its
fixed producer-table size, chosen before every original risk/depth input. -/
def truePort (prefixCap : ℕ) : Fin (prefixCap+Spatial.MulCap.cap+2) :=
  PSTRTMSeq005.rightLabel (a:=prefixCap)
    (PSTRTMSeq005.rightLabel (a:=Spatial.MulCap.packetCap) (1365 : Fin 1583))
def falsePort (prefixCap : ℕ) : Fin (prefixCap+Spatial.MulCap.cap+2) :=
  PSTRTMSeq005.rightLabel (a:=prefixCap)
    (PSTRTMSeq005.rightLabel (a:=Spatial.MulCap.packetCap) (1582 : Fin 1583))

def dispatch (prefixCap : ℕ) (q : Fin (prefixCap+Spatial.MulCap.cap+2)) : Option (Fin 220) :=
  if q.val=(truePort prefixCap).val then some entryTrue
  else if q.val=(falsePort prefixCap).val then some entryFalse else none

theorem distinct_ports (prefixCap : ℕ) : (falsePort prefixCap).val≠(truePort prefixCap).val := by
  simp only [truePort,falsePort,PSTRTMSeq005.rightLabel,
    show (1365 : Fin 1583).val=1365 by decide,show (1582 : Fin 1583).val=1582 by decide]
  omega
theorem dispatch_true (prefixCap : ℕ) : dispatch prefixCap (truePort prefixCap)=some entryTrue := by
  unfold dispatch
  rw [ite_eq_left rfl]
theorem dispatch_false (prefixCap : ℕ) : dispatch prefixCap (falsePort prefixCap)=some entryFalse := by
  unfold dispatch
  rw [ite_eq_right (distinct_ports prefixCap),ite_eq_left rfl]

theorem actual_port (prefixCap : ℕ) (x y : Rat) (positive : 0<x*y) :
    PSTRTMSeq005.rightLabel (a:=prefixCap) (Spatial.MulCap.final x y).q=
      if (1/4 : Rat)≤x*y then truePort prefixCap else falsePort prefixCap := by
  have control:=Spatial.MulCap.final_control x y positive
  apply Fin.ext
  by_cases capped : (1/4 : Rat)≤x*y
  · simp only [capped,ite_true,truePort,PSTRTMSeq005.rightLabel,
      show (1365 : Fin 1583).val=1365 by decide]
    rw [control]
    simp only [capped,ite_true]
  · simp only [capped,ite_false,falsePort,PSTRTMSeq005.rightLabel,
      show (1582 : Fin 1583).val=1582 by decide]
    rw [control]
    simp only [capped,ite_false]

/-- Dispatch reads the actual saved HALT port. No branch answer is an
input datum, and an unconditional Seq005 reset is deliberately absent. -/
theorem actual_dispatch (prefixCap : ℕ) (x y : Rat) (positive : 0<x*y) :
    dispatch prefixCap (PSTRTMSeq005.rightLabel (a:=prefixCap) (Spatial.MulCap.final x y).q)=
      some (entry (decide ((1/4 : Rat)≤x*y))) := by
  rw [actual_port prefixCap x y positive]
  by_cases capped : (1/4 : Rat)≤x*y
  · have choice : decide ((1/4 : Rat)≤x*y)=true := by simp only [capped,decide_true]
    rw [ite_eq_left capped,choice]
    exact dispatch_true prefixCap
  · have choice : decide ((1/4 : Rat)≤x*y)=false := by simp only [capped,decide_false]
    rw [ite_eq_right capped,choice]
    exact dispatch_false prefixCap

end RootB23.Threshold.ReturnDispatch
