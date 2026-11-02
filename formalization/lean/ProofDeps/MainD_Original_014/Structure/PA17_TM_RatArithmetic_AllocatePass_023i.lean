module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023h

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018 PA17TMRatArithmeticAllocate013

def fieldExit (k : Nat) : Fin (fieldCap k+1) :=
  label (p:=1) (s:=cycleCap k) 0 (padLabel (cycleCap_ge k) (1 : Fin 4))

theorem field_pass_bounded (k : Nat) (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool)
    (followingWidth : Nat) (routes : PassRoutes out back outPort backPort rest footer followingWidth)
    (left digits : List Bool) (n : Nat) :
    BoundedRun (fieldPassMachine k (passCycleMachine k out back))
      (Turing.Tape.mk₂ left (nxStream digits (false::rest (gapTail n)))) (fieldExit k)
      (Turing.Tape.mk₂ (pushField left digits) (false::rest (gapTail (n+k*digits.length))))
      (digits.length*(2*n+(2*k+4)*digits.length+4*followingWidth+4*k+51)+2) := by
  obtain ⟨trace,hr,hl⟩ := fieldPass_runsFrom k out back outPort backPort rest footer followingWidth routes left n [] digits
  change PSTRTMSeq005.RunsFrom (fieldPassMachine k (passCycleMachine k out back))
    (blockCfg (s:=cycleCap k) (0 : Fin 2)
      ⟨0,Turing.Tape.mk₂ left (nxStream digits (false::rest (gapTail n)))⟩) trace
    (blockCfg (s:=cycleCap k) (0 : Fin 2) (padCfg (cycleCap_ge k)
      ⟨(1 : Fin 4),Turing.Tape.mk₂ (pushField left digits) (false::rest (gapTail (n+k*digits.length)))⟩)) at hr
  rw [blockCfg_zero] at hr
  exact ⟨trace,hr,hl⟩

def nxPassFieldMachine (k : Nat) : Machine (fieldCap k) := fieldPassMachine k (passCycleMachine k outNxCode returnNxCode)
def dxPassFieldMachine (k : Nat) : Machine (fieldCap k) := fieldPassMachine k (passCycleMachine k outDxCode returnDxCode)
def nyPassFieldMachine (k : Nat) : Machine (fieldCap k) := fieldPassMachine k (passCycleMachine k outNyCode returnNyCode)
def dyPassFieldMachine (k : Nat) : Machine (fieldCap k) := fieldPassMachine k (passCycleMachine k outDyCode returnDyCode)

def firstPairCap (k : Nat) : Nat := fieldCap k+fieldCap k+1
def yHeaderCap (k : Nat) : Nat := firstPairCap k+2+1
def thirdFieldCap (k : Nat) : Nat := yHeaderCap k+fieldCap k+1
def fourFieldCap (k : Nat) : Nat := thirdFieldCap k+fieldCap k+1
def rawPassCap (k : Nat) : Nat := fourFieldCap k+34+1
def passCap (k : Nat) : Nat := 120*k+581

def firstPairPassMachine (k : Nat) : Machine (firstPairCap k) :=
  PSTRTMSeq005.seqMachine (nxPassFieldMachine k) (dxPassFieldMachine k)
def yHeaderPassMachine (k : Nat) : Machine (yHeaderCap k) :=
  PSTRTMSeq005.seqMachine (firstPairPassMachine k) headerRightMachine
def thirdFieldPassMachine (k : Nat) : Machine (thirdFieldCap k) :=
  PSTRTMSeq005.seqMachine (yHeaderPassMachine k) (nyPassFieldMachine k)
def fourFieldPassMachine (k : Nat) : Machine (fourFieldCap k) :=
  PSTRTMSeq005.seqMachine (thirdFieldPassMachine k) (dyPassFieldMachine k)
def rawPassMachine (k : Nat) : Machine (rawPassCap k) :=
  PSTRTMSeq005.seqMachine (fourFieldPassMachine k) finishBackMachine

theorem rawPassCap_eq (k : Nat) : rawPassCap k=passCap k := by
  unfold rawPassCap fourFieldCap thirdFieldCap yHeaderCap firstPairCap fieldCap cycleCap cycleBackCap outExpandCap
    passCap expandCap totalStates
  omega

/-- Equal-cap static reindexing only; no cursor/content operation. This
public literal cap is the stable finite-control ABI consumed by Root025. -/
def passMachine (k : Nat) : Machine (passCap k) :=
  padMachine (Nat.le_of_eq (rawPassCap_eq k)) (rawPassMachine k)

def passFee (k W n : Nat) : Nat := W*(2*n+(2*k+4)*W+4*k+64)+48

theorem pass_cap_literal (k : Nat) : passCap k=120*k+581 := rfl

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
