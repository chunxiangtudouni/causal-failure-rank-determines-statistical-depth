module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036d

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033
open PA17TMRatArithmeticAllocatePass023 (restoreBackMachine restoreBackTrace restoreBack_runsFrom)

/-- Source layouts and costs describe the actual frozen route code; the
opaque suffix is not a zero gap and never becomes an executable argument. -/
structure FramedSourceRoutes (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool)
    (followingWidth : Nat) : Prop where
  out_run : ∀ left later suffix, BoundedRun (s:=26) out
    (Tape.mk₂ left (nxStream later (false::rest suffix))) outPort
    (Tape.mk₂ (footer left later) (false::suffix)) (2*(later.length+followingWidth)+11)
  back_run : ∀ archive later suffix, BoundedRun (s:=26) back
    (Tape.mk₂ (footer (false::archive) later) (false::suffix)) backPort
    (Tape.mk₂ (false::archive) (nxStream later (false::rest suffix))) (2*(later.length+followingWidth)+23)

def outBankCap (j k : Nat) : Nat := 26+bankRoundCap j k+1
def backCycleCap (j k : Nat) : Nat := outBankCap j k+26+1
def cachedCycleCap (j k : Nat) : Nat := backCycleCap j k+3+1
attribute [local implicit_reducible] outBankCap backCycleCap cachedCycleCap

theorem cachedCycleCap_eq (j k : Nat) : cachedCycleCap j k=15*k+22*j+77 := by
  unfold cachedCycleCap backCycleCap outBankCap
  rw [bankRoundCap_eq]
  omega

theorem cachedCycleCap_ge (j k : Nat) : 3≤cachedCycleCap j k := by
  unfold cachedCycleCap backCycleCap outBankCap
  omega

def outBankMachine (j k : Nat) (out : Machine 26) : Machine (outBankCap j k) :=
  PSTRTMSeq005.seqMachine out (bankRoundMachine j k)
def backCycleMachine (j k : Nat) (out back : Machine 26) : Machine (backCycleCap j k) :=
  PSTRTMSeq005.seqMachine (outBankMachine j k out) back
def cachedCycleMachine (j k : Nat) (out back : Machine 26) : Machine (cachedCycleCap j k) :=
  PSTRTMSeq005.seqMachine (backCycleMachine j k out back) restoreBackMachine

def cycleSurcharge (j : Nat) (records : List RecordSpec) (followingWidth : Nat) : Nat :=
  4*followingWidth+2*totalGap records+4*totalWidth records+21*j+57

/-- An observed source flag buys a real cached-bank growth, then the
actual source marker is restored by LEFT/WRITE_TRUE/RIGHT. Every route,
cached cursor, marker write, allocator operation and HALT is paid. -/
theorem cached_cycle_bounded (j k : Nat) (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool) (followingWidth : Nat)
    (routes : FramedSourceRoutes out back outPort backPort rest footer followingWidth)
    (records : List RecordSpec) (hj : records.length=j) (archive later : List Bool) (n : Nat) :
    BoundedRun (s:=cachedCycleCap j k) (cachedCycleMachine j k out back)
      (Tape.mk₂ (false::archive) (nxStream later (false::rest (bankTail records (gapWord n)))))
      (Fin.last (cachedCycleCap j k))
      (Tape.mk₂ (true::archive) (nxStream later (false::rest (bankTail records (gapWord (n+k))))))
      (4*later.length+2*n+4*k+cycleSurcharge j records followingWidth) := by
  let input := Tape.mk₂ (false::archive) (nxStream later (false::rest (bankTail records (gapWord n))))
  let bankArchive := footer (false::archive) later
  have ho := routes.out_run (false::archive) later (bankTail records (gapWord n))
  have hg := bank_round_bounded j k records hj bankArchive n
  have hfirst : BoundedRun (s:=outBankCap j k) (outBankMachine j k out) input
      (PSTRTMSeq005.rightLabel (a:=26) (Fin.last (bankRoundCap j k)))
      (bankTape bankArchive records (n+k))
      ((2*(later.length+followingWidth)+11)+bankRoundFee j k records n) := ho.seq hg
  have hb := routes.back_run archive later (bankTail records (gapWord (n+k)))
  have hsecond : BoundedRun (s:=backCycleCap j k) (backCycleMachine j k out back) input
      (PSTRTMSeq005.rightLabel (a:=outBankCap j k) backPort)
      (Tape.mk₂ (false::archive) (nxStream later (false::rest (bankTail records (gapWord (n+k))))))
      (((2*(later.length+followingWidth)+11)+bankRoundFee j k records n)+
        (2*(later.length+followingWidth)+23)) := hfirst.seq hb
  have hs : BoundedRun (s:=3) restoreBackMachine
      (Tape.mk₂ (false::archive) (nxStream later (false::rest (bankTail records (gapWord (n+k)))))) 3
      (Tape.mk₂ (true::archive) (nxStream later (false::rest (bankTail records (gapWord (n+k)))))) 4 :=
    ⟨restoreBackTrace archive (nxStream later (false::rest (bankTail records (gapWord (n+k))))),
     restoreBack_runsFrom archive (nxStream later (false::rest (bankTail records (gapWord (n+k))))),by rfl⟩
  exact (hsecond.seq hs).mono (by unfold bankRoundFee cycleSurcharge;omega)

theorem cached_cycle_contract (j k : Nat) (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool) (followingWidth : Nat)
    (routes : FramedSourceRoutes out back outPort backPort rest footer followingWidth)
    (records : List RecordSpec) (hj : records.length=j) :
    SourceCycleContract (cachedCycleCap j k) (cachedCycleMachine j k out back) k
      (cycleSurcharge j records followingWidth) (fun n => rest (bankTail records (gapWord n))) := by
  intro archive later n
  exact cached_cycle_bounded j k out back outPort backPort rest footer followingWidth routes records hj archive later n

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
