module
public import Structure.PA17_TM_RatArithmetic_Width_018h

/-! The complete four-field producer starts at the clamped Nx data cell
and finishes at the original input header. An existing left counter n is
incremented by the four physical flag counts; all source cells and the
arbitrary suffix beyond the original FALSE footer are restored verbatim. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticParse002

def bank (nx dx ny dy suffix : List Bool) : List Bool :=
  nxStream nx (nxStream dx (false::false::nxStream ny (nxStream dy (false::suffix))))
def bankWidth (nx dx ny dy : List Bool) : Nat := nx.length+dx.length+ny.length+dy.length

def finishBackMachine : Machine 34 := PSTRTMSeq005.seqMachine fieldBackMachine backDyMachine

theorem finishBack_bounded (sx : Bool) (counter nx dx ny dy suffix : List Bool) :
    BoundedRun finishBackMachine
      (Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks dy.reverse++false::dyContext sx counter nx dx ny))
        (false::suffix)) 34
      (Turing.Tape.mk₂ counter (prefixRight sx (bank nx dx ny dy suffix)))
      (2*bankWidth nx dx ny dy+31) := by
  have hf : BoundedRun fieldBackMachine
      (Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks dy.reverse++false::dyContext sx counter nx dx ny))
        (false::suffix)) 5
      (Turing.Tape.mk₂ (false::dyContext sx counter nx dx ny) (nxStream dy (false::suffix))) (2*dy.length+5) :=
    ⟨fieldBackTrace (dyContext sx counter nx dx ny) dy (false::suffix),
     fieldBack_runsFrom (dyContext sx counter nx dx ny) dy (false::suffix),
     by rw [fieldBackTrace_length]⟩
  have hb : BoundedRun backDyMachine
      (Turing.Tape.mk₂ (false::dyContext sx counter nx dx ny) (nxStream dy (false::suffix))) 28
      (Turing.Tape.mk₂ counter (prefixRight sx (bank nx dx ny dy suffix)))
      (2*(nx.length+dx.length+ny.length)+26) :=
    ⟨backDyTrace sx counter nx dx ny (nxStream dy (false::suffix)),
     backDy_runsFrom sx counter nx dx ny (nxStream dy (false::suffix)),
     by rw [backDyTrace_length]⟩
  exact (hf.seq hb).mono (by unfold bankWidth;omega)

def firstPairMachine : Machine 303 := PSTRTMSeq005.seqMachine nxCounterMachine dxCounterMachine
def yHeaderMachine : Machine 306 := PSTRTMSeq005.seqMachine firstPairMachine headerRightMachine
def thirdFieldMachine : Machine 458 := PSTRTMSeq005.seqMachine yHeaderMachine nyCounterMachine
def fourFieldMachine : Machine 610 := PSTRTMSeq005.seqMachine thirdFieldMachine dyCounterMachine
def middleMachine : Machine 645 := PSTRTMSeq005.seqMachine fourFieldMachine finishBackMachine

theorem fieldCost_le (n previous width total : Nat) (h : previous+width≤total) :
    width*(2*(n+previous)+6*width+4*previous+64)+2 ≤ width*(2*n+6*total+64)+2 := by
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  omega

/-- Reusable middle entry. It does not rerun parsing, inspect the later
workspace, accept a width/fuel answer, or replace a tape by an isolated
copy. Its only data-dependent count is the actual frozen counter trace. -/
theorem middle_bounded (sx : Bool) (n : Nat) (nxTail dxTail nyTail dyTail suffix : List Bool) :
    BoundedRun middleMachine
      (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones n))
        (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) suffix)) 645
      (Turing.Tape.mk₂
        (false::ROOTTMGCDCounter011.ones (n+bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)))
        (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) suffix)))
      (bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)*
        (2*n+6*bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)+68)+48) := by
  let nx := false::nxTail
  let dx := false::dxTail
  let ny := false::nyTail
  let dy := false::dyTail
  let w := bankWidth nx dx ny dy
  let n1 := n+nx.length
  let n2 := n1+dx.length
  let n3 := n2+ny.length
  let n4 := n3+dy.length
  let rdy := nxStream dy (false::suffix)
  let rny := nxStream ny rdy
  have hx := fieldCounter_bounded backNxCode forwardNxCode 7 7
    (fun k => nxContext sx (false::ROOTTMGCDCounter011.ones k)) (prefixRight sx) 0
    (nx_routes sx) n nxTail (true::(PSTRTMIncrement009.blocks dxTail++false::false::false::rny))
  have hd := fieldCounter_bounded backDxCode forwardDxCode 13 9
    (fun k => dxContext sx (false::ROOTTMGCDCounter011.ones k) nx)
    (fun right => prefixRight sx (nxStream nx right)) nx.length
    (dx_routes sx nx) n1 dxTail (false::rny)
  have hh : BoundedRun headerRightMachine
      (Turing.Tape.mk₂ (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx (false::ROOTTMGCDCounter011.ones n2) nx))
        (false::false::rny)) 2
      (Turing.Tape.mk₂ (false::nyContext sx (false::ROOTTMGCDCounter011.ones n2) nx dx) rny) 3 :=
    ⟨headerRightTrace (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx (false::ROOTTMGCDCounter011.ones n2) nx))
       false false rny,
     headerRight_runsFrom (false::(PSTRTMRawNat010.leftBlocks dx.reverse++false::dxContext sx (false::ROOTTMGCDCounter011.ones n2) nx))
       false false rny,by rfl⟩
  have hy := fieldCounter_bounded backNyCode forwardNyCode 22 14
    (fun k => nyContext sx (false::ROOTTMGCDCounter011.ones k) nx dx)
    (fun right => prefixRight sx (nyStream nx dx right)) (nx.length+dx.length)
    (ny_routes sx nx dxTail) n2 nyTail (true::(PSTRTMIncrement009.blocks dyTail++false::false::suffix))
  have he := fieldCounter_bounded backDyCode forwardDyCode 28 16
    (fun k => dyContext sx (false::ROOTTMGCDCounter011.ones k) nx dx ny)
    (fun right => prefixRight sx (dyStream nx dx ny right)) (nx.length+dx.length+ny.length)
    (dy_routes sx nx dxTail ny) n3 dyTail suffix
  have hf := finishBack_bounded sx (false::ROOTTMGCDCounter011.ones n4) nx dx ny dy suffix
  have hr := ((((hx.seq hd).seq hh).seq hy).seq he).seq hf
  have hn : n4=n+w := by dsimp [n4,n3,n2,n1,w,bankWidth];omega
  have hc1 := fieldCost_le n 0 nx.length w (by dsimp [w,bankWidth];omega)
  have hc2 := fieldCost_le n nx.length dx.length w (by dsimp [w,bankWidth];omega)
  have hc3 := fieldCost_le n (nx.length+dx.length) ny.length w (by dsimp [w,bankWidth];omega)
  have hc4 := fieldCost_le n (nx.length+dx.length+ny.length) dy.length w (by dsimp [w,bankWidth];omega)
  have hbound :
      (nx.length*(2*n+6*nx.length+4*0+64)+2)+
      (dx.length*(2*n1+6*dx.length+4*nx.length+64)+2)+3+
      (ny.length*(2*n2+6*ny.length+4*(nx.length+dx.length)+64)+2)+
      (dy.length*(2*n3+6*dy.length+4*(nx.length+dx.length+ny.length)+64)+2)+
      (2*w+31) ≤ w*(2*n+6*w+68)+48 := by
    dsimp [n1,n2,n3,w,bankWidth] at hc1 hc2 hc3 hc4 ⊢
    nlinarith
  have hr' := hr.mono hbound
  have hbank : bank nx dx ny dy suffix = PSTRTMIncrement009.blocks nx ++
      false::false::true::(PSTRTMIncrement009.blocks dxTail++false::false::false::rny) := rfl
  change BoundedRun middleMachine
    (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones n))
      (PSTRTMIncrement009.blocks nx ++
        false::false::true::(PSTRTMIncrement009.blocks dxTail++false::false::false::rny))) 645
    (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones n4) (prefixRight sx (bank nx dx ny dy suffix)))
    (w*(2*n+6*w+68)+48) at hr'
  rw [←hbank,hn] at hr'
  exact hr'

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
