module
public import Structure.PA17_TM_RatArithmetic_CachedPass_036e

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticAllocatePass023

/-! The frozen source routes retain an arbitrary suffix. Cached words
are never treated as blank; only the paid bank round grows its far gap. -/
theorem dy_source_routes : FramedSourceRoutes outDyCode returnDyCode 1 5 dyRest dyFooter 0 := by
  constructor
  · intro left later suffix
    have h : BoundedRun outDyMachine (Turing.Tape.mk₂ left (nxStream later (false::dyRest (suffix)))) 1
        (Turing.Tape.mk₂ (dyFooter left later) (false::suffix)) (2*later.length+2) :=
      ⟨outDyTrace left later (suffix),outDy_runsFrom left later (suffix),by rw [outDyTrace_length]⟩
    exact (h.pad (by decide : 1≤26)).mono (by omega)
  · intro archive later suffix
    have h : BoundedRun returnDyMachine
        (Turing.Tape.mk₂ (dyFooter (false::archive) later) (false::suffix)) 5
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::dyRest (suffix)))) (2*later.length+5) :=
      ⟨returnDyTrace archive later (false::suffix),returnDy_runsFrom archive later (false::suffix),
       by rw [returnDyTrace_length]⟩
    exact (h.pad (by decide : 5≤26)).mono (by omega)

theorem ny_source_routes (dyTail : List Bool) : FramedSourceRoutes outNyCode returnNyCode 3 11
    (nyRest dyTail) (nyFooter dyTail) (false::dyTail).length := by
  constructor
  · intro left later suffix
    have h : BoundedRun outNyMachine
        (Turing.Tape.mk₂ left (nxStream later (false::nyRest dyTail (suffix)))) 3
        (Turing.Tape.mk₂ (nyFooter dyTail left later) (false::suffix))
        (2*(later.length+(false::dyTail).length)+4) :=
      ⟨outNyTrace left later dyTail (suffix),outNy_runsFrom left later dyTail (suffix),
       by rw [outNyTrace_length]⟩
    exact (h.pad (by decide : 3≤26)).mono (by omega)
  · intro archive later suffix
    have h : BoundedRun returnNyMachine
        (Turing.Tape.mk₂ (nyFooter dyTail (false::archive) later) (false::suffix)) 11
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::nyRest dyTail (suffix))))
        (2*(later.length+(false::dyTail).length)+10) :=
      ⟨returnNyTrace archive later (false::dyTail) (false::suffix),
       returnNy_runsFrom archive later (false::dyTail) (false::suffix),by rw [returnNyTrace_length]⟩
    exact (h.pad (by decide : 11≤26)).mono (by omega)

theorem dx_source_routes (nyTail dyTail : List Bool) : FramedSourceRoutes outDxCode returnDxCode 8 20
    (dxRest nyTail dyTail) (dxFooter nyTail dyTail) ((false::nyTail).length+(false::dyTail).length) := by
  constructor
  · intro left later suffix
    have h : BoundedRun outDxMachine
        (Turing.Tape.mk₂ left (nxStream later (false::dxRest nyTail dyTail (suffix)))) 8
        (Turing.Tape.mk₂ (dxFooter nyTail dyTail left later) (false::suffix))
        (2*(later.length+(false::nyTail).length+(false::dyTail).length)+9) :=
      ⟨outDxTrace left later nyTail dyTail (suffix),outDx_runsFrom left later nyTail dyTail (suffix),
       by rw [outDxTrace_length]⟩
    exact (h.pad (by decide : 8≤26)).mono (by omega)
  · intro archive later suffix
    have h : BoundedRun returnDxMachine
        (Turing.Tape.mk₂ (dxFooter nyTail dyTail (false::archive) later) (false::suffix)) 20
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::dxRest nyTail dyTail (suffix))))
        (2*(later.length+(false::nyTail).length+(false::dyTail).length)+18) :=
      ⟨returnDxTrace archive later (false::nyTail) (false::dyTail) (false::suffix),
       returnDx_runsFrom archive later (false::nyTail) (false::dyTail) (false::suffix),by rw [returnDxTrace_length]⟩
    exact (h.pad (by decide : 20≤26)).mono (by omega)

theorem nx_source_routes (dxTail nyTail dyTail : List Bool) : FramedSourceRoutes outNxCode returnNxCode 10 26
    (nxRest dxTail nyTail dyTail) (nxFooter dxTail nyTail dyTail)
    ((false::dxTail).length+(false::nyTail).length+(false::dyTail).length) := by
  constructor
  · intro left later suffix
    have h : BoundedRun outNxMachine
        (Turing.Tape.mk₂ left (nxStream later (false::nxRest dxTail nyTail dyTail (suffix)))) 10
        (Turing.Tape.mk₂ (nxFooter dxTail nyTail dyTail left later) (false::suffix))
        (2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+11) :=
      ⟨outNxTrace left later dxTail nyTail dyTail (suffix),outNx_runsFrom left later dxTail nyTail dyTail (suffix),
       by rw [outNxTrace_length]⟩
    exact (h.pad (by decide : 10≤26)).mono (by omega)
  · intro archive later suffix
    have h : BoundedRun returnNxMachine
        (Turing.Tape.mk₂ (nxFooter dxTail nyTail dyTail (false::archive) later) (false::suffix)) 26
        (Turing.Tape.mk₂ (false::archive) (nxStream later (false::nxRest dxTail nyTail dyTail (suffix))))
        (2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23) :=
      ⟨returnNxTrace archive later (false::dxTail) (false::nyTail) (false::dyTail) (false::suffix),
       returnNx_runsFrom archive later (false::dxTail) (false::nyTail) (false::dyTail) (false::suffix),
       by rw [returnNxTrace_length]⟩
    exact h.mono (by omega)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticCachedPass036
