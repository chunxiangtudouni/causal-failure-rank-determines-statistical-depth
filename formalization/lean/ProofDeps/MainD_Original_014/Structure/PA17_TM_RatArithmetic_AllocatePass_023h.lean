module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023g

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018

def outDyCode : Machine 26 := padMachine (by decide : 1≤26) outDyMachine
def outNyCode : Machine 26 := padMachine (by decide : 3≤26) outNyMachine
def outDxCode : Machine 26 := padMachine (by decide : 8≤26) outDxMachine
def outNxCode : Machine 26 := padMachine (by decide : 10≤26) outNxMachine
def returnDyCode : Machine 26 := padMachine (by decide : 5≤26) returnDyMachine
def returnNyCode : Machine 26 := padMachine (by decide : 11≤26) returnNyMachine
def returnDxCode : Machine 26 := padMachine (by decide : 20≤26) returnDxMachine
def returnNxCode : Machine 26 := returnNxMachine

def dyRest (suffix : List Bool) : List Bool := suffix
def dyFooter (left later : List Bool) : List Bool := pushField left later
def nyRest (dyTail suffix : List Bool) : List Bool := true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix)
def nyFooter (dyTail left later : List Bool) : List Bool := pushField (pushField left later) (false::dyTail)
def dxRest (nyTail dyTail suffix : List Bool) : List Bool :=
  false::nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))
def dxFooter (nyTail dyTail left later : List Bool) : List Bool :=
  pushField (pushField (yHeaderLeft (pushField left later)) (false::nyTail)) (false::dyTail)
def nxRest (dxTail nyTail dyTail suffix : List Bool) : List Bool :=
  true::(PSTRTMIncrement009.blocks dxTail++false::false::false::
    nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))
def nxFooter (dxTail nyTail dyTail left later : List Bool) : List Bool :=
  pushField (pushField (yHeaderLeft (pushField (pushField left later) (false::dxTail)))
    (false::nyTail)) (false::dyTail)

theorem dy_pass_routes : PassRoutes outDyCode returnDyCode 1 5 dyRest dyFooter 0 := by
  constructor
  · intro left later n
    have h : BoundedRun outDyMachine (Turing.Tape.mk₂ left (nxStream later (false::dyRest (gapTail n)))) 1
        (Turing.Tape.mk₂ (dyFooter left later) (false::gapTail n)) (2*later.length+2) :=
      ⟨outDyTrace left later (gapTail n),outDy_runsFrom left later (gapTail n),by rw [outDyTrace_length]⟩
    exact (h.pad (by decide : 1≤26)).mono (by omega)
  · intro archive later n
    have h : BoundedRun returnDyMachine
        (Turing.Tape.mk₂ (dyFooter (false::archive) later) (false::gapTail n)) 5
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::dyRest (gapTail n)))) (2*later.length+5) :=
      ⟨returnDyTrace archive later (false::gapTail n),returnDy_runsFrom archive later (false::gapTail n),
       by rw [returnDyTrace_length]⟩
    exact (h.pad (by decide : 5≤26)).mono (by omega)

theorem ny_pass_routes (dyTail : List Bool) : PassRoutes outNyCode returnNyCode 3 11
    (nyRest dyTail) (nyFooter dyTail) (false::dyTail).length := by
  constructor
  · intro left later n
    have h : BoundedRun outNyMachine
        (Turing.Tape.mk₂ left (nxStream later (false::nyRest dyTail (gapTail n)))) 3
        (Turing.Tape.mk₂ (nyFooter dyTail left later) (false::gapTail n))
        (2*(later.length+(false::dyTail).length)+4) :=
      ⟨outNyTrace left later dyTail (gapTail n),outNy_runsFrom left later dyTail (gapTail n),
       by rw [outNyTrace_length]⟩
    exact (h.pad (by decide : 3≤26)).mono (by omega)
  · intro archive later n
    have h : BoundedRun returnNyMachine
        (Turing.Tape.mk₂ (nyFooter dyTail (false::archive) later) (false::gapTail n)) 11
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::nyRest dyTail (gapTail n))))
        (2*(later.length+(false::dyTail).length)+10) :=
      ⟨returnNyTrace archive later (false::dyTail) (false::gapTail n),
       returnNy_runsFrom archive later (false::dyTail) (false::gapTail n),by rw [returnNyTrace_length]⟩
    exact (h.pad (by decide : 11≤26)).mono (by omega)

theorem dx_pass_routes (nyTail dyTail : List Bool) : PassRoutes outDxCode returnDxCode 8 20
    (dxRest nyTail dyTail) (dxFooter nyTail dyTail) ((false::nyTail).length+(false::dyTail).length) := by
  constructor
  · intro left later n
    have h : BoundedRun outDxMachine
        (Turing.Tape.mk₂ left (nxStream later (false::dxRest nyTail dyTail (gapTail n)))) 8
        (Turing.Tape.mk₂ (dxFooter nyTail dyTail left later) (false::gapTail n))
        (2*(later.length+(false::nyTail).length+(false::dyTail).length)+9) :=
      ⟨outDxTrace left later nyTail dyTail (gapTail n),outDx_runsFrom left later nyTail dyTail (gapTail n),
       by rw [outDxTrace_length]⟩
    exact (h.pad (by decide : 8≤26)).mono (by omega)
  · intro archive later n
    have h : BoundedRun returnDxMachine
        (Turing.Tape.mk₂ (dxFooter nyTail dyTail (false::archive) later) (false::gapTail n)) 20
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::dxRest nyTail dyTail (gapTail n))))
        (2*(later.length+(false::nyTail).length+(false::dyTail).length)+18) :=
      ⟨returnDxTrace archive later (false::nyTail) (false::dyTail) (false::gapTail n),
       returnDx_runsFrom archive later (false::nyTail) (false::dyTail) (false::gapTail n),by rw [returnDxTrace_length]⟩
    exact (h.pad (by decide : 20≤26)).mono (by omega)

theorem nx_pass_routes (dxTail nyTail dyTail : List Bool) : PassRoutes outNxCode returnNxCode 10 26
    (nxRest dxTail nyTail dyTail) (nxFooter dxTail nyTail dyTail)
    ((false::dxTail).length+(false::nyTail).length+(false::dyTail).length) := by
  constructor
  · intro left later n
    have h : BoundedRun outNxMachine
        (Turing.Tape.mk₂ left (nxStream later (false::nxRest dxTail nyTail dyTail (gapTail n)))) 10
        (Turing.Tape.mk₂ (nxFooter dxTail nyTail dyTail left later) (false::gapTail n))
        (2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+11) :=
      ⟨outNxTrace left later dxTail nyTail dyTail (gapTail n),outNx_runsFrom left later dxTail nyTail dyTail (gapTail n),
       by rw [outNxTrace_length]⟩
    exact (h.pad (by decide : 10≤26)).mono (by omega)
  · intro archive later n
    have h : BoundedRun returnNxMachine
        (Turing.Tape.mk₂ (nxFooter dxTail nyTail dyTail (false::archive) later) (false::gapTail n)) 26
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::nxRest dxTail nyTail dyTail (gapTail n))))
        (2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23) :=
      ⟨returnNxTrace archive later (false::dxTail) (false::nyTail) (false::dyTail) (false::gapTail n),
       returnNx_runsFrom archive later (false::dxTail) (false::nyTail) (false::dyTail) (false::gapTail n),
       by rw [returnNxTrace_length]⟩
    exact h.mono (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
