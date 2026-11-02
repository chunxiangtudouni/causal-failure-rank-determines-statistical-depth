module

public import RootB236_RiskFold_Paths002
public import Structure.RootB23_Threshold_ReturnOriginalActual_057
public import Common.PSTR_WordBool_RatOutputLink_079

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace RootB236.RiskFold

open Turing PaperProofs.Common.Native
open PaperProofs.Common.Native.RationalControllerComputation

theorem frozen_threshold_actual (risk : Rat) (depth : Nat) (positive : 0<risk) (depthPositive : 1≤depth) :
    ∃ (left : Nat) (trace : List (MachineState RootB23.Threshold.ReturnOriginalPacket.cap)),
      Runs RootB23.Threshold.ReturnOriginalPacket.code (encode [.rational risk,.natural depth]) trace
        ⟨RootB23.Threshold.ReturnOriginalPacket.finalPort,RootB23.Threshold.ReturnOriginalPacket.finalTape risk depth left⟩ ∧
      trace.length≤RootB23.Threshold.ReturnOriginalPacket.timeCoefficient*
        RootB23.Threshold.OriginalBridge.scale risk depth^10 := by
  obtain ⟨left,trace,run,time,_,_⟩ := RootB23.Threshold.ReturnOriginalPacket.actual risk depth positive depthPositive
  exact ⟨left,trace,run,time⟩

def frozen_threshold_bridge :
    PSTRWordBool.IsolatedRat.Label → PSTRWordBool.IsolatedRat.Statement Unit RootB23.Threshold.ReturnOriginalPacket.cap :=
  PSTRWordBool.IsolatedRat.program RootB23.Threshold.ReturnOriginalPacket.code .halt

end RootB236.RiskFold
