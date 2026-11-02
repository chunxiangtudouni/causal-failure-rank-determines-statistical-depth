module
public import Common.ROOT_TM_GCD_Lift_020
public import Common.ROOT_TM_GCD_PairStep_019

set_option autoImplicit false
set_option warningAsError true
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLeg021
open PaperProofs.Common.Native.RationalControllerComputation
open PA17TMDivisionCompose006 ROOTTMGCDDispatch018 ROOTTMGCDLift020
local notation "cols" => PSTRTMBinaryAdd024.operandColumns

/-- A genuine phase segment together with its actual final transfer.
The transfer is charged when the next segment is appended, with no duplicate
states and no assumed head reset or reload of numeric data. -/
def Leg (first : MachineState 3219) (trace : List (MachineState 3219))
    (next : MachineState 3219) : Prop :=
  ∃ last, Segment residentGcdMachine first trace last ∧
    Turing.TM0.step residentGcdMachine last=some next

theorem Leg.append (first middle next : MachineState 3219)
    (xs ys : List (MachineState 3219)) (hx : Leg first xs middle) (hy : Leg middle ys next) :
    Leg first (xs++ys) next := by
  obtain ⟨lastLeft,hl,ht⟩:=hx
  obtain ⟨lastRight,hr,hu⟩:=hy
  exact ⟨lastRight,segment_append residentGcdMachine first lastLeft middle lastRight xs ys hl hr ht,hu⟩

def cfgAt (phase : Fin 23) (n : Nat) (pairs : List (Bool × Bool)) (suffix : List Bool) : MachineState 3219 :=
  blockCfg (s:=139) phase ⟨0,Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (cols pairs++false::false::suffix)⟩

def halfTrace (phase : Fin 23) (n : Nat) (pairs : List (Bool × Bool)) (suffix : List Bool) : List (MachineState 3219) :=
  (ROOTTMGCDHalfResident014.trace (ROOTTMGCDCounter011.ones n) pairs suffix).map (lift (by decide : 52 ≤ 139) phase)

theorem half_leg (phase next : Fin 23)
    (hf : family phase=padMachine (by decide : 52 ≤ 139) ROOTTMGCDHalfResident014.residentHalfMachine)
    (hp : ∀ r : Fin 4, ports phase ⟨49+r.val,by have h:=r.isLt; omega⟩=some (next,0))
    (n : Nat) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    Leg (cfgAt phase n pairs suffix) (halfTrace phase n pairs suffix)
      (cfgAt next n (ROOTTMGCDHalf001.halfPairs pairs) suffix) := by
  let archive:=ROOTTMGCDCounter011.ones n
  have run:=ROOTTMGCDHalfResident014.residentHalf_runsFrom archive pairs suffix
  have hs:=phase_segment (by decide : 52 ≤ 139) phase ROOTTMGCDHalfResident014.residentHalfMachine
    hf _ _ _ run
  have hport : ports phase (padLabel (by decide : 52 ≤ 139) (ROOTTMGCDHalfResident014.final archive pairs suffix).q)=some (next,0) :=
    by
      let r:=ROOTTMGCDHalf001.finalControl (ROOTTMGCDHalf001.carryControl false false) pairs.reverse
      have hlabel : padLabel (by decide : 52 ≤ 139) (ROOTTMGCDHalfResident014.final archive pairs suffix).q=
          (⟨49+r.val,by have h:=r.isLt; omega⟩ : Fin 140) := by
        apply Fin.ext
        change 28+(21+r.val)=49+r.val
        omega
      rw [hlabel]
      exact hp r
  have ht:=phase_transfer (by decide : 52 ≤ 139) phase next ROOTTMGCDHalfResident014.residentHalfMachine
    hf _ run.2.2.2 0 hport
  exact ⟨lift (by decide : 52 ≤ 139) phase (ROOTTMGCDHalfResident014.final archive pairs suffix),hs,ht⟩

theorem evenB_leg (n : Nat) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    Leg (cfgAt 2 n pairs suffix) (halfTrace 2 n pairs suffix)
      (cfgAt 0 n (ROOTTMGCDHalf001.halfPairs pairs) suffix) := by
  apply half_leg 2 0 (by rfl)
  intro r
  have hr:=r.isLt
  simp [ports,show 49 ≤ 49+r.val by omega,show 49+r.val ≤ 52 by omega]

theorem halfTrace_length (phase : Fin 23) (n : Nat) (pairs : List (Bool × Bool)) (suffix : List Bool) :
    (halfTrace phase n pairs suffix).length=9*pairs.length+6 := by
  simp only [halfTrace,List.length_map,ROOTTMGCDHalfResident014.residentHalf_length]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDLeg021
