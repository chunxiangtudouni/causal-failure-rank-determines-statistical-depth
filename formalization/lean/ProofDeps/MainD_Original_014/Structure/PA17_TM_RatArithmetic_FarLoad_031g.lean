module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031f

/-! Four fixed original-field route tables. Following field lengths and
contents occur in RouteCorrect, never in these executable machines. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticAllocatePass023
open PA17TMRatArithmeticWidth018 (BoundedRun nxStream)

theorem bounded_pad {a s : Nat} (h : a≤s) {machine : Machine a}
    {first last : Tape Bool} {q : Fin (a+1)} {bound : Nat}
    (run : BoundedRun machine first q last bound) :
    BoundedRun (padMachine h machine) first (padLabel h q) last bound := by
  obtain ⟨trace,hr,hl⟩ := run
  exact ⟨trace.map (padCfg h),pad_runsFrom h machine _ _ _ hr,
    by simpa only [List.length_map] using hl⟩

def dyRoute : FarRoute :=
  ⟨padMachine (by decide) outDyMachine,padMachine (by decide) returnDyMachine,
    padLabel (by decide : 1≤10) 1,padLabel (by decide : 5≤26) 5⟩
def nyRoute : FarRoute :=
  ⟨padMachine (by decide) outNyMachine,padMachine (by decide) returnNyMachine,
    padLabel (by decide : 3≤10) 3,padLabel (by decide : 11≤26) 11⟩
def dxRoute : FarRoute :=
  ⟨padMachine (by decide) outDxMachine,padMachine (by decide) returnDxMachine,
    padLabel (by decide : 8≤10) 8,padLabel (by decide : 20≤26) 20⟩
def nxRoute : FarRoute := ⟨outNxMachine,returnNxMachine,10,26⟩

def dyFinish (left digits : List Bool) : List Bool := pushField left digits
def nyContext (dyTail : List Bool) : List Bool := nxStream (false::dyTail) []
def nyFinish (dyTail left digits : List Bool) : List Bool :=
  pushField (pushField left digits) (false::dyTail)
def dxContext (nyTail dyTail : List Bool) : List Bool :=
  false::false::nxStream (false::nyTail) (nxStream (false::dyTail) [])
def dxFinish (nyTail dyTail left digits : List Bool) : List Bool :=
  pushField (pushField (yHeaderLeft (pushField left digits)) (false::nyTail)) (false::dyTail)
def nxContext (dxTail nyTail dyTail : List Bool) : List Bool :=
  nxStream (false::dxTail) (dxContext nyTail dyTail)
def nxFinish (dxTail nyTail dyTail left digits : List Bool) : List Bool :=
  pushField (pushField (yHeaderLeft (pushField (pushField left digits) (false::dxTail)))
    (false::nyTail)) (false::dyTail)

theorem pushField_cons (left : List Bool) (bit : Bool) (later : List Bool) :
    pushField (true::bit::left) later=pushField left (bit::later) := by
  simp only [pushField,PSTRTMRawNat010.leftBlocks,List.reverse_cons,List.flatMap_append,
    List.flatMap_cons,List.flatMap_nil,List.cons_append,List.nil_append,List.append_assoc]

theorem dy_route_correct : RouteCorrect dyRoute [] dyFinish 5 := by
  refine ⟨rfl,?_,?_,?_⟩
  · exact pushField_cons
  · intro left later suffix
    have h : BoundedRun outDyMachine (Tape.mk₂ left (nxStream later (false::suffix))) 1
        (Tape.mk₂ (pushField left later) (false::suffix)) (2*later.length+2) :=
      ⟨outDyTrace left later suffix,outDy_runsFrom left later suffix,by rw [outDyTrace_length]⟩
    exact (bounded_pad (by decide : 1≤10) h).mono (by omega)
  · intro archive later suffix
    have h : BoundedRun returnDyMachine
        (Tape.mk₂ (pushField (false::archive) later) (false::suffix)) 5
        (Tape.mk₂ (false::archive) (nxStream later (false::suffix))) (2*later.length+5) :=
      ⟨returnDyTrace archive later (false::suffix),returnDy_runsFrom archive later (false::suffix),
        by rw [returnDyTrace_length]⟩
    exact bounded_pad (by decide : 5≤26) h

theorem ny_route_correct (dyTail : List Bool) :
    RouteCorrect nyRoute (nyContext dyTail) (nyFinish dyTail) (2*(false::dyTail).length+10) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro left bit later
    simp only [nyFinish,pushField_cons]
  · intro left later suffix
    have h : BoundedRun outNyMachine
        (Tape.mk₂ left (nxStream later (nxStream (false::dyTail) (false::suffix)))) 3
        (Tape.mk₂ (nyFinish dyTail left later) (false::suffix))
        (2*(later.length+(false::dyTail).length)+4) :=
      ⟨outNyTrace left later dyTail suffix,outNy_runsFrom left later dyTail suffix,by rw [outNyTrace_length]⟩
    have hp := (bounded_pad (by decide : 3≤10) h).mono
      (by omega : 2*(later.length+(false::dyTail).length)+4≤2*later.length+(2*(false::dyTail).length+10))
    simpa only [nyRoute,fieldWord,nyContext,nxStream,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using hp
  · intro archive later suffix
    have h : BoundedRun returnNyMachine
        (Tape.mk₂ (nyFinish dyTail (false::archive) later) (false::suffix)) 11
        (Tape.mk₂ (false::archive) (nxStream later (nxStream (false::dyTail) (false::suffix))))
        (2*(later.length+(false::dyTail).length)+10) :=
      ⟨returnNyTrace archive later (false::dyTail) (false::suffix),
        returnNy_runsFrom archive later (false::dyTail) (false::suffix),by rw [returnNyTrace_length]⟩
    have hp := (bounded_pad (by decide : 11≤26) h).mono
      (by omega : 2*(later.length+(false::dyTail).length)+10≤2*later.length+(2*(false::dyTail).length+10))
    simpa only [nyRoute,fieldWord,nyContext,nxStream,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using hp

theorem dx_route_correct (nyTail dyTail : List Bool) :
    RouteCorrect dxRoute (dxContext nyTail dyTail) (dxFinish nyTail dyTail)
      (2*((false::nyTail).length+(false::dyTail).length)+18) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro left bit later
    simp only [dxFinish,pushField_cons]
  · intro left later suffix
    have h : BoundedRun outDxMachine
        (Tape.mk₂ left (nxStream later (false::false::nxStream (false::nyTail)
          (nxStream (false::dyTail) (false::suffix))))) 8
        (Tape.mk₂ (dxFinish nyTail dyTail left later) (false::suffix))
        (2*(later.length+(false::nyTail).length+(false::dyTail).length)+9) :=
      ⟨outDxTrace left later nyTail dyTail suffix,outDx_runsFrom left later nyTail dyTail suffix,
        by rw [outDxTrace_length]⟩
    have hp := (bounded_pad (by decide : 8≤10) h).mono
      (by omega : 2*(later.length+(false::nyTail).length+(false::dyTail).length)+9≤
        2*later.length+(2*((false::nyTail).length+(false::dyTail).length)+18))
    simpa only [dxRoute,fieldWord,dxContext,nxStream,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using hp
  · intro archive later suffix
    have h : BoundedRun returnDxMachine
        (Tape.mk₂ (dxFinish nyTail dyTail (false::archive) later) (false::suffix)) 20
        (Tape.mk₂ (false::archive) (nxStream later (false::false::nxStream (false::nyTail)
          (nxStream (false::dyTail) (false::suffix)))))
        (2*(later.length+(false::nyTail).length+(false::dyTail).length)+18) :=
      ⟨returnDxTrace archive later (false::nyTail) (false::dyTail) (false::suffix),
        returnDx_runsFrom archive later (false::nyTail) (false::dyTail) (false::suffix),by rw [returnDxTrace_length]⟩
    have hp := (bounded_pad (by decide : 20≤26) h).mono
      (by omega : 2*(later.length+(false::nyTail).length+(false::dyTail).length)+18≤
        2*later.length+(2*((false::nyTail).length+(false::dyTail).length)+18))
    simpa only [dxRoute,fieldWord,dxContext,nxStream,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using hp

theorem nx_route_correct (dxTail nyTail dyTail : List Bool) :
    RouteCorrect nxRoute (nxContext dxTail nyTail dyTail) (nxFinish dxTail nyTail dyTail)
      (2*((false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23) := by
  refine ⟨rfl,?_,?_,?_⟩
  · intro left bit later
    simp only [nxFinish,pushField_cons]
  · intro left later suffix
    have h : BoundedRun outNxMachine
        (Tape.mk₂ left (nxStream later (nxStream (false::dxTail) (false::false::
          nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix)))))) 10
        (Tape.mk₂ (nxFinish dxTail nyTail dyTail left later) (false::suffix))
        (2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+11) :=
      ⟨outNxTrace left later dxTail nyTail dyTail suffix,
        outNx_runsFrom left later dxTail nyTail dyTail suffix,by rw [outNxTrace_length]⟩
    have hp := h.mono
      (by omega : 2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+11≤
        2*later.length+(2*((false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23))
    simpa only [nxRoute,fieldWord,nxContext,dxContext,nxStream,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using hp
  · intro archive later suffix
    have h : BoundedRun returnNxMachine
        (Tape.mk₂ (nxFinish dxTail nyTail dyTail (false::archive) later) (false::suffix)) 26
        (Tape.mk₂ (false::archive) (nxStream later (nxStream (false::dxTail) (false::false::
          nxStream (false::nyTail) (nxStream (false::dyTail) (false::suffix))))))
        (2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23) :=
      ⟨returnNxTrace archive later (false::dxTail) (false::nyTail) (false::dyTail) (false::suffix),
        returnNx_runsFrom archive later (false::dxTail) (false::nyTail) (false::dyTail) (false::suffix),
        by rw [returnNxTrace_length]⟩
    have hp := h.mono
      (by omega : 2*(later.length+(false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23≤
        2*later.length+(2*((false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23))
    simpa only [nxRoute,fieldWord,nxContext,dxContext,nxStream,List.append_assoc,List.nil_append,List.append_nil,
      List.cons_append] using hp

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
