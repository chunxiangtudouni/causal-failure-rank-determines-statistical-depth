module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023e

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocate013.expandCap
attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMRatArithmeticWidth018 PA17TMRatArithmeticAllocate013

/-- These functions describe whole tapes of fixed route code. They never
occur in that executable code or supply a width, fuel or numeric answer. -/
structure PassRoutes (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool)
    (followingWidth : Nat) : Prop where
  out_run : ∀ left later n, BoundedRun out
    (Turing.Tape.mk₂ left (nxStream later (false::rest (gapTail n)))) outPort
    (Turing.Tape.mk₂ (footer left later) (false::gapTail n)) (2*(later.length+followingWidth)+11)
  back_run : ∀ archive later n, BoundedRun back
    (Turing.Tape.mk₂ (footer (false::archive) later) (false::gapTail n)) backPort
    (Turing.Tape.mk₂ (false::archive) (nxStream later (false::rest (gapTail n)))) (2*(later.length+followingWidth)+23)

def outExpandCap (k : Nat) : Nat := 26+expandCap k+1
def cycleBackCap (k : Nat) : Nat := outExpandCap k+26+1
def cycleCap (k : Nat) : Nat := cycleBackCap k+3+1

theorem cycleCap_eq (k : Nat) : cycleCap k=expandCap k+58 := by
  unfold cycleCap cycleBackCap outExpandCap
  omega

theorem cycleCap_ge (k : Nat) : 3≤cycleCap k := by rw [cycleCap_eq];omega

def outExpandMachine (k : Nat) (out : Machine 26) : Machine (outExpandCap k) :=
  PSTRTMSeq005.seqMachine out (expandMachine k)
def cycleBackMachine (k : Nat) (out back : Machine 26) : Machine (cycleBackCap k) :=
  PSTRTMSeq005.seqMachine (outExpandMachine k out) back
def passCycleMachine (k : Nat) (out back : Machine 26) : Machine (cycleCap k) :=
  PSTRTMSeq005.seqMachine (cycleBackMachine k out back) restoreBackMachine

theorem expand_bounded (k n : Nat) (archive : List Bool) :
    BoundedRun (expandMachine k) (Turing.Tape.mk₂ archive (false::gapTail n))
      (expandLast k n archive).q (Turing.Tape.mk₂ archive (false::gapTail (n+k))) (2*n+4*k+9) := by
  refine ⟨expandTrace k n archive,?_,?_⟩
  · have hr := expand_runsFrom k n archive
    rw [expand_first_zero] at hr
    change PSTRTMSeq005.RunsFrom (expandMachine k)
      ⟨0,Turing.Tape.mk₂ archive (false::gapTail n)⟩ (expandTrace k n archive)
      ⟨(expandLast k n archive).q,Turing.Tape.mk₂ archive (false::gapTail (k+n))⟩ at hr
    simpa only [Nat.add_comm k n] using hr
  · rw [expand_length]

/-- One source flag buys one real k-cell expansion. The source marker is
restored only after the actual return to its next-data cell. All callee
HALTs and transfers are paid in this exhibited SAME-code trace. -/
theorem passCycle_bounded (k : Nat) (out back : Machine 26) (outPort backPort : Fin 27)
    (rest : List Bool → List Bool) (footer : List Bool → List Bool → List Bool)
    (followingWidth : Nat) (routes : PassRoutes out back outPort backPort rest footer followingWidth)
    (archive later : List Bool) (n : Nat) :
    BoundedRun (passCycleMachine k out back)
      (Turing.Tape.mk₂ (false::archive) (nxStream later (false::rest (gapTail n))))
      (Fin.last (cycleCap k))
      (Turing.Tape.mk₂ (true::archive) (nxStream later (false::rest (gapTail (n+k)))))
      (4*(later.length+followingWidth)+2*n+4*k+47) := by
  have ho := routes.out_run (false::archive) later n
  have he := expand_bounded k n (footer (false::archive) later)
  have hb := routes.back_run archive later (n+k)
  have hs : BoundedRun restoreBackMachine
      (Turing.Tape.mk₂ (false::archive) (nxStream later (false::rest (gapTail (n+k))))) 3
      (Turing.Tape.mk₂ (true::archive) (nxStream later (false::rest (gapTail (n+k))))) 4 :=
    ⟨restoreBackTrace archive (nxStream later (false::rest (gapTail (n+k)))),
     restoreBack_runsFrom archive (nxStream later (false::rest (gapTail (n+k)))),by rfl⟩
  have hr := ((ho.seq he).seq hb).seq hs
  apply hr.mono
  omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
