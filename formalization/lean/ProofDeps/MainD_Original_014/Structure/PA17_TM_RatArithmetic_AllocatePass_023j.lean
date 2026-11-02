module
public import Structure.PA17_TM_RatArithmetic_AllocatePass_023i

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
open PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018

attribute [local implicit_reducible] fieldCap cycleCap firstPairCap yHeaderCap thirdFieldCap fourFieldCap rawPassCap

theorem passFieldCost_le (k n previous width following total : Nat)
    (hp : previous+width≤total) (hf : width+following≤total) :
    width*(2*(n+k*previous)+(2*k+4)*width+4*following+4*k+51)+2 ≤
      width*(2*n+(2*k+4)*total+4*k+51)+2 := by
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  have hk := Nat.mul_le_mul_left (2*k) hp
  nlinarith

def passTraceFee (k n a b c d : Nat) : Nat :=
      (a*(2*n+(2*k+4)*a+4*(b+c+d)+4*k+51)+2)+
      (b*(2*(n+k*a)+(2*k+4)*b+4*(c+d)+4*k+51)+2)+3+
      (c*(2*(n+k*a+k*b)+(2*k+4)*c+4*d+4*k+51)+2)+
      (d*(2*(n+k*a+k*b+k*c)+(2*k+4)*d+4*0+4*k+51)+2)+(2*(a+b+c+d)+31)

theorem passTraceFee_le (k n a b c d : Nat) :
    passTraceFee k n a b c d ≤ passFee k (a+b+c+d) n := by
  let W := a+b+c+d
  let n1 := n+k*a
  let n2 := n1+k*b
  let n3 := n2+k*c
  have hc1 := passFieldCost_le k n 0 a (b+c+d) W
    (by dsimp [W];omega) (by dsimp [W];omega)
  have hc2 := passFieldCost_le k n a b (c+d) W
    (by dsimp [W];omega) (by dsimp [W];omega)
  have hc3 := passFieldCost_le k n (a+b) c d W
    (by dsimp [W];omega) (by dsimp [W];omega)
  have hc4 := passFieldCost_le k n (a+b+c) d 0 W
    (by dsimp [W];omega) (by dsimp [W];omega)
  have hbound :
      (a*(2*n+(2*k+4)*a+4*(b+c+d)+4*k+51)+2)+
      (b*(2*n1+(2*k+4)*b+4*(c+d)+4*k+51)+2)+3+
      (c*(2*n2+(2*k+4)*c+4*d+4*k+51)+2)+
      (d*(2*n3+(2*k+4)*d+4*0+4*k+51)+2)+(2*W+31) ≤ passFee k W n := by
    dsimp [n1,n2,n3,W,passFee] at hc1 hc2 hc3 hc4 ⊢
    nlinarith
  exact hbound

private def fieldFee (k n width following : Nat) : Nat :=
  width*(2*n+(2*k+4)*width+4*following+4*k+51)+2

private def pairFee (k n : Nat) (nx dx ny dy : List Bool) : Nat :=
  fieldFee k n nx.length (dx.length+ny.length+dy.length)+
    fieldFee k (n+k*nx.length) dx.length (ny.length+dy.length)
private def threeFee (k n : Nat) (nx dx ny dy : List Bool) : Nat :=
  pairFee k n nx dx ny dy+3+
    fieldFee k (n+k*nx.length+k*dx.length) ny.length dy.length
private def fourFee (k n : Nat) (nx dx ny dy : List Bool) : Nat :=
  threeFee k n nx dx ny dy+
    fieldFee k (n+k*nx.length+k*dx.length+k*ny.length) dy.length 0

private def startTape (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::nxContext sx counter) (bank nx dx ny dy (gapTail n))
private def dxTape (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::dxContext sx counter nx)
    (nxStream dx (false::false::nxStream ny (nxStream dy (false::gapTail n))))
private def yHeaderTape (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (pushField (false::dxContext sx counter nx) dx)
    (false::false::nxStream ny (nxStream dy (false::gapTail n)))
private def nyTape (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::nyContext sx counter nx dx) (nxStream ny (nxStream dy (false::gapTail n)))
private def dyTape (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (false::dyContext sx counter nx dx ny) (nxStream dy (false::gapTail n))
private def footerTape (sx : Bool) (counter nx dx ny dy : List Bool) (n : Nat) : Turing.Tape Bool :=
  Turing.Tape.mk₂ (pushField (false::dyContext sx counter nx dx ny) dy) (false::gapTail n)

/-- A folded two-field interface avoids comparing the full machine at every later transfer. -/
private theorem pair_pass_bounded (k : Nat) (sx : Bool) (counter : List Bool) (n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    let nx := false::nxTail; let dx := false::dxTail
    let ny := false::nyTail; let dy := false::dyTail
    BoundedRun (firstPairPassMachine k) (startTape sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=fieldCap k) (fieldExit k))
      (yHeaderTape sx counter nx dx ny dy (n+k*nx.length+k*dx.length))
      (pairFee k n nx dx ny dy) := by
  dsimp only
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  have hx : BoundedRun (nxPassFieldMachine k) (startTape sx counter nx dx ny dy n) (fieldExit k)
      (dxTape sx counter nx dx ny dy (n+k*nx.length))
      (fieldFee k n nx.length (dx.length+ny.length+dy.length)) :=
    field_pass_bounded k outNxCode returnNxCode 10 26 (nxRest dxTail nyTail dyTail)
      (nxFooter dxTail nyTail dyTail) (dx.length+ny.length+dy.length) (nx_pass_routes dxTail nyTail dyTail)
      (false::nxContext sx counter) nx n
  have hd : BoundedRun (dxPassFieldMachine k) (dxTape sx counter nx dx ny dy (n+k*nx.length)) (fieldExit k)
      (yHeaderTape sx counter nx dx ny dy (n+k*nx.length+k*dx.length))
      (fieldFee k (n+k*nx.length) dx.length (ny.length+dy.length)) :=
    field_pass_bounded k outDxCode returnDxCode 8 20 (dxRest nyTail dyTail) (dxFooter nyTail dyTail)
      (ny.length+dy.length) (dx_pass_routes nyTail dyTail) (false::dxContext sx counter nx) dx (n+k*nx.length)
  exact hx.seq hd

private theorem three_pass_bounded (k : Nat) (sx : Bool) (counter : List Bool) (n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    let nx := false::nxTail; let dx := false::dxTail
    let ny := false::nyTail; let dy := false::dyTail
    BoundedRun (thirdFieldPassMachine k) (startTape sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=yHeaderCap k) (fieldExit k))
      (dyTape sx counter nx dx ny dy (n+k*nx.length+k*dx.length+k*ny.length))
      (threeFee k n nx dx ny dy) := by
  dsimp only
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  let n2 := n+k*nx.length+k*dx.length
  have hp := pair_pass_bounded k sx counter n nxTail dxTail nyTail dyTail
  have hh : BoundedRun headerRightMachine (yHeaderTape sx counter nx dx ny dy n2) 2
      (nyTape sx counter nx dx ny dy n2) 3 :=
    ⟨headerRightTrace (pushField (false::dxContext sx counter nx) dx) false false
       (nxStream ny (nxStream dy (false::gapTail n2))),
     headerRight_runsFrom (pushField (false::dxContext sx counter nx) dx) false false
       (nxStream ny (nxStream dy (false::gapTail n2))),by rfl⟩
  have hb : BoundedRun (yHeaderPassMachine k) (startTape sx counter nx dx ny dy n) 
      (PSTRTMSeq005.rightLabel (a:=firstPairCap k) (2 : Fin 3))
      (nyTape sx counter nx dx ny dy n2) (pairFee k n nx dx ny dy+3) := hp.seq hh
  have hy : BoundedRun (nyPassFieldMachine k) (nyTape sx counter nx dx ny dy n2) (fieldExit k)
      (dyTape sx counter nx dx ny dy (n2+k*ny.length))
      (fieldFee k n2 ny.length dy.length) :=
    field_pass_bounded k outNyCode returnNyCode 3 11 (nyRest dyTail) (nyFooter dyTail) dy.length
      (ny_pass_routes dyTail) (false::nyContext sx counter nx dx) ny n2
  exact hb.seq hy

private theorem four_pass_bounded (k : Nat) (sx : Bool) (counter : List Bool) (n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    let nx := false::nxTail; let dx := false::dxTail
    let ny := false::nyTail; let dy := false::dyTail
    BoundedRun (fourFieldPassMachine k) (startTape sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=thirdFieldCap k) (fieldExit k))
      (footerTape sx counter nx dx ny dy (n+k*nx.length+k*dx.length+k*ny.length+k*dy.length))
      (fourFee k n nx dx ny dy) := by
  dsimp only
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  let n3 := n+k*nx.length+k*dx.length+k*ny.length
  have ht := three_pass_bounded k sx counter n nxTail dxTail nyTail dyTail
  have hd : BoundedRun (dyPassFieldMachine k) (dyTape sx counter nx dx ny dy n3) (fieldExit k)
      (footerTape sx counter nx dx ny dy (n3+k*dy.length)) (fieldFee k n3 dy.length 0) :=
    field_pass_bounded k outDyCode returnDyCode 1 5 dyRest dyFooter 0 dy_pass_routes
      (false::dyContext sx counter nx dx ny) dy n3
  exact ht.seq hd

/-- The complete original-bank pass, with only folded component interfaces
at the final actual transfer. All moves, flag writes and HALTs are paid. -/
theorem raw_pass_bounded (k : Nat) (sx : Bool) (h n : Nat)
    (nxTail dxTail nyTail dyTail : List Bool) :
    BoundedRun (rawPassMachine k)
      (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones h))
        (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) (gapTail n)))
      (Fin.last (rawPassCap k))
      (Turing.Tape.mk₂ (false::ROOTTMGCDCounter011.ones h)
        (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)
          (gapTail (n+k*bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail))))))
      (passFee k (bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)) n) := by
  let nx := false::nxTail; let dx := false::dxTail
  let ny := false::nyTail; let dy := false::dyTail
  let counter := false::ROOTTMGCDCounter011.ones h
  let n4 := n+k*nx.length+k*dx.length+k*ny.length+k*dy.length
  have hs := four_pass_bounded k sx counter n nxTail dxTail nyTail dyTail
  have hf := finishBack_bounded sx counter nx dx ny dy (gapTail n4)
  have hr : BoundedRun (rawPassMachine k) (startTape sx counter nx dx ny dy n)
      (PSTRTMSeq005.rightLabel (a:=fourFieldCap k) (34 : Fin 35))
      (Turing.Tape.mk₂ counter (prefixRight sx (bank nx dx ny dy (gapTail n4))))
      (fourFee k n nx dx ny dy+(2*bankWidth nx dx ny dy+31)) := hs.seq hf
  have hq : PSTRTMSeq005.rightLabel (a:=fourFieldCap k) (34 : Fin 35)=Fin.last (rawPassCap k) := by
    apply Fin.ext
    change fourFieldCap k+1+34=fourFieldCap k+34+1
    omega
  have hn : n4=n+k*bankWidth nx dx ny dy := by
    dsimp [n4,bankWidth]
    ring
  rw [hq,hn] at hr
  have hb : fourFee k n nx dx ny dy+(2*bankWidth nx dx ny dy+31) ≤
      passFee k (bankWidth nx dx ny dy) n :=
    passTraceFee_le k n nx.length dx.length ny.length dy.length
  exact hr.mono hb

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticAllocatePass023
