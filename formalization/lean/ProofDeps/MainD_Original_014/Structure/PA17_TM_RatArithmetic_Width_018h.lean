module
public import Structure.PA17_TM_RatArithmetic_Width_018g

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
open PA17TMDivisionCompose006

theorem BoundedRun.pad {a s : Nat} (h : a≤s) {machine : Machine a} {input output : Turing.Tape Bool}
    {q : Fin (a+1)} {bound : Nat} (run : BoundedRun machine input q output bound) :
    BoundedRun (padMachine h machine) input (padLabel h q) output bound := by
  obtain ⟨trace,hr,hl⟩ := run
  refine ⟨trace.map (padCfg h),?_,?_⟩
  · have hp := pad_runsFrom h machine ⟨0,input⟩ ⟨q,output⟩ trace hr
    rw [PA17TMRatArithmeticBookmark014.pad_zero] at hp
    exact hp
  · simpa only [List.length_map] using hl

theorem false_head (right : List Bool) (h : right.head?=some false) : ∃ tail, right=false::tail := by
  cases right with
  | nil => simp at h
  | cons bit tail =>
    have hb : bit=false := Option.some.inj h
    exact ⟨tail,by rw [hb]⟩

def backNxCode : Machine 28 := padMachine (by decide : 7≤28) backNxMachine
def backDxCode : Machine 28 := padMachine (by decide : 13≤28) backDxMachine
def backNyCode : Machine 28 := padMachine (by decide : 22≤28) backNyMachine
def backDyCode : Machine 28 := backDyMachine
def forwardNxCode : Machine 28 := padMachine (by decide : 7≤28) forwardNxMachine
def forwardDxCode : Machine 28 := padMachine (by decide : 9≤28) forwardDxMachine
def forwardNyCode : Machine 28 := padMachine (by decide : 14≤28) forwardNyMachine
def forwardDyCode : Machine 28 := padMachine (by decide : 16≤28) forwardDyMachine

theorem nx_routes (sx : Bool) : RouteSpec backNxCode forwardNxCode 7 7
    (fun n => nxContext sx (false::ROOTTMGCDCounter011.ones n)) (prefixRight sx) 0 := by
  constructor
  · intro n right
    have h : BoundedRun backNxMachine
        (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones n)) right) 7
        (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (prefixRight sx right)) 8 :=
      ⟨backNxTrace sx (false::ROOTTMGCDCounter011.ones n) right,
       backNx_runsFrom sx (false::ROOTTMGCDCounter011.ones n) right,
       by rw [backNxTrace_length]⟩
    exact (h.pad (by decide : 7≤28)).mono (by omega)
  · intro n right _
    have h : BoundedRun forwardNxMachine
        (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (prefixRight sx right)) 7
        (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones n)) right) 8 :=
      ⟨forwardNxTrace sx (false::ROOTTMGCDCounter011.ones n) right,
       forwardNx_runsFrom sx (false::ROOTTMGCDCounter011.ones n) right,
       by rw [forwardNxTrace_length]⟩
    exact (h.pad (by decide : 7≤28)).mono (by omega)

theorem dx_routes (sx : Bool) (nx : List Bool) : RouteSpec backDxCode forwardDxCode 13 9
    (fun n => dxContext sx (false::ROOTTMGCDCounter011.ones n) nx)
    (fun right => prefixRight sx (nxStream nx right)) nx.length := by
  constructor
  · intro n right
    have h : BoundedRun backDxMachine
        (Turing.Tape.mk₂ (false::dxContext sx (false::ROOTTMGCDCounter011.ones n) nx) right) 13
        (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (prefixRight sx (nxStream nx right))) (2*nx.length+13) :=
      ⟨backDxTrace sx (false::ROOTTMGCDCounter011.ones n) nx right,
       backDx_runsFrom sx (false::ROOTTMGCDCounter011.ones n) nx right,
       by rw [backDxTrace_length]⟩
    exact (h.pad (by decide : 13≤28)).mono (by omega)
  · intro n right hz
    obtain ⟨tail,rfl⟩ := false_head right hz
    have h : BoundedRun forwardDxMachine
        (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (prefixRight sx (nxStream nx (false::tail)))) 9
        (Turing.Tape.mk₂ (false::dxContext sx (false::ROOTTMGCDCounter011.ones n) nx) (false::tail)) (2*nx.length+10) :=
      ⟨forwardDxTrace sx (false::ROOTTMGCDCounter011.ones n) nx tail,
       forwardDx_runsFrom sx (false::ROOTTMGCDCounter011.ones n) nx tail,
       by rw [forwardDxTrace_length]⟩
    exact (h.pad (by decide : 9≤28)).mono (by omega)

theorem ny_routes (sx : Bool) (nx dxTail : List Bool) : RouteSpec backNyCode forwardNyCode 22 14
    (fun n => nyContext sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail))
    (fun right => prefixRight sx (nyStream nx (false::dxTail) right)) (nx.length+(false::dxTail).length) := by
  constructor
  · intro n right
    have h : BoundedRun backNyMachine
        (Turing.Tape.mk₂ (false::nyContext sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail)) right) 22
        (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (prefixRight sx (nyStream nx (false::dxTail) right)))
        (2*(nx.length+(false::dxTail).length)+21) :=
      ⟨backNyTrace sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail) right,
       backNy_runsFrom sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail) right,
       by rw [backNyTrace_length]⟩
    exact (h.pad (by decide : 22≤28)).mono (by omega)
  · intro n right _
    have h : BoundedRun forwardNyMachine
        (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n) (prefixRight sx (nyStream nx (false::dxTail) right))) 14
        (Turing.Tape.mk₂ (false::nyContext sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail)) right)
        (2*(nx.length+(false::dxTail).length)+15) :=
      ⟨forwardNyTrace sx (false::ROOTTMGCDCounter011.ones n) nx dxTail right,
       forwardNy_runsFrom sx (false::ROOTTMGCDCounter011.ones n) nx dxTail right,
       by rw [forwardNyTrace_length]⟩
    exact (h.pad (by decide : 14≤28)).mono (by omega)

theorem dy_routes (sx : Bool) (nx dxTail ny : List Bool) : RouteSpec backDyCode forwardDyCode 28 16
    (fun n => dyContext sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail) ny)
    (fun right => prefixRight sx (dyStream nx (false::dxTail) ny right))
    (nx.length+(false::dxTail).length+ny.length) := by
  constructor
  · intro n right
    exact ⟨backDyTrace sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail) ny right,
      backDy_runsFrom sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail) ny right,
      by rw [backDyTrace_length]⟩
  · intro n right hz
    obtain ⟨tail,rfl⟩ := false_head right hz
    have h : BoundedRun forwardDyMachine
        (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n)
          (prefixRight sx (dyStream nx (false::dxTail) ny (false::tail)))) 16
        (Turing.Tape.mk₂ (false::dyContext sx (false::ROOTTMGCDCounter011.ones n) nx (false::dxTail) ny) (false::tail))
        (2*(nx.length+(false::dxTail).length+ny.length)+17) :=
      ⟨forwardDyTrace sx (false::ROOTTMGCDCounter011.ones n) nx dxTail ny tail,
       forwardDy_runsFrom sx (false::ROOTTMGCDCounter011.ones n) nx dxTail ny tail,
       by rw [forwardDyTrace_length]⟩
    exact h.pad (by decide : 16≤28)

theorem fieldCounter_bounded (back forward : Machine 28) (backPort forwardPort : Fin 29)
    (archive : Nat → List Bool) (home : List Bool → List Bool) (previousWidth : Nat)
    (routes : RouteSpec back forward backPort forwardPort archive home previousWidth)
    (n : Nat) (fieldTail suffix : List Bool) :
    BoundedRun (fieldCounterMachine (cycleMachine back forward))
      (Turing.Tape.mk₂ (false::archive n) (PSTRTMIncrement009.blocks (false::fieldTail)++false::false::suffix)) 1
      (Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks (false::fieldTail).reverse++
        false::archive (n+(false::fieldTail).length))) (false::suffix))
      ((false::fieldTail).length*(2*n+6*(false::fieldTail).length+4*previousWidth+64)+2) := by
  obtain ⟨trace,hr,hl⟩ := fieldCounter_runsFrom back forward backPort forwardPort archive home previousWidth
    routes n [] (false::fieldTail) suffix fieldTail rfl
  refine ⟨trace,hr,?_⟩
  simpa only [List.length_nil,Nat.mul_zero,Nat.add_zero] using hl

def nxCounterMachine : Machine 151 := fieldCounterMachine (cycleMachine backNxCode forwardNxCode)
def dxCounterMachine : Machine 151 := fieldCounterMachine (cycleMachine backDxCode forwardDxCode)
def nyCounterMachine : Machine 151 := fieldCounterMachine (cycleMachine backNyCode forwardNyCode)
def dyCounterMachine : Machine 151 := fieldCounterMachine (cycleMachine backDyCode forwardDyCode)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
