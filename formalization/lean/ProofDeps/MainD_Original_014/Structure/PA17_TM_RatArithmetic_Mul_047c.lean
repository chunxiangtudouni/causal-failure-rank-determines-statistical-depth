module
public import Structure.PA17_TM_RatArithmetic_Mul_047b
public import Structure.PA17_TM_RatArithmetic_FarLoad_031i

/-! Multiplication chain, stage 3: the SAME frozen original-field navigation
programs with an arbitrary already-produced footer suffix. Only the proof is
extended from031's blank workspace; no navigation code or loader is rewritten. -/
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMul047

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticFarLoad031
open PA17TMRatArithmeticWidth018 (BoundedRun)

def sourceHeaderTape (sx : Bool) (counter nxTail dxTail nyTail dyTail suffix : List Bool) : Tape Bool :=
  Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx
    (sourceBank nxTail dxTail nyTail dyTail suffix))

theorem source_navigation_with_suffix_bounded (field : SourceField) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (suffix : List Bool) :
    BoundedRun (sourceNavigation field) (sourceHeaderTape sx counter nxTail dxTail nyTail dyTail suffix)
      (sourcePort field)
      (Tape.mk₂ (false::sourceArchive field sx counter nxTail dxTail nyTail)
        (fieldWord (sourceContext field dxTail nyTail dyTail)
          (false::sourceTail field nxTail dxTail nyTail dyTail) suffix))
      (navigationFee nxTail dxTail nyTail) := by
  cases field with
  | dy =>
    let tail := (fieldWord [] (false::dyTail) suffix).tail
    have h : BoundedRun PA17TMRatArithmeticWidth018.forwardDyMachine
        (Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx
          (PA17TMRatArithmeticWidth018.dyStream (false::nxTail) (false::dxTail) (false::nyTail) (false::tail)))) 16
        (Tape.mk₂ (false::PA17TMRatArithmeticWidth018.dyContext sx counter (false::nxTail)
          (false::dxTail) (false::nyTail)) (false::tail))
        (2*((false::nxTail).length+(false::dxTail).length+(false::nyTail).length)+17) :=
      ⟨PA17TMRatArithmeticWidth018.forwardDyTrace sx counter (false::nxTail) dxTail (false::nyTail) tail,
        PA17TMRatArithmeticWidth018.forwardDy_runsFrom sx counter (false::nxTail) dxTail (false::nyTail) tail,
        by rw [PA17TMRatArithmeticWidth018.forwardDyTrace_length]⟩
    simpa only [sourceNavigation,sourcePort,sourceHeaderTape,sourceBank,sourceArchive,sourceContext,sourceTail,
      navigationFee,tail,fieldWord,nxContext,dxContext,PA17TMRatArithmeticWidth018.dyStream,
      PA17TMRatArithmeticWidth018.nyStream,PA17TMRatArithmeticWidth018.nxStream,
      PSTRTMIncrement009.blocks,List.flatMap_cons,List.cons_append,List.nil_append,List.append_nil,
      List.append_assoc,List.tail_cons] using h
  | ny =>
    let right := fieldWord (nyContext dyTail) (false::nyTail) suffix
    have h : BoundedRun PA17TMRatArithmeticWidth018.forwardNyMachine
        (Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx
          (PA17TMRatArithmeticWidth018.nyStream (false::nxTail) (false::dxTail) right))) 14
        (Tape.mk₂ (false::PA17TMRatArithmeticWidth018.nyContext sx counter (false::nxTail) (false::dxTail)) right)
        (2*((false::nxTail).length+(false::dxTail).length)+15) :=
      ⟨PA17TMRatArithmeticWidth018.forwardNyTrace sx counter (false::nxTail) dxTail right,
        PA17TMRatArithmeticWidth018.forwardNy_runsFrom sx counter (false::nxTail) dxTail right,
        by rw [PA17TMRatArithmeticWidth018.forwardNyTrace_length]⟩
    have hp := (bounded_pad (by decide : 14≤16) h).mono
      (by unfold navigationFee; omega : 2*((false::nxTail).length+(false::dxTail).length)+15≤ navigationFee nxTail dxTail nyTail)
    have hport : padLabel (by decide : 14≤16) (14 : Fin 15)=(14 : Fin 17) := by decide
    rw [hport] at hp
    simpa only [sourceNavigation,sourcePort,sourceHeaderTape,sourceBank,sourceArchive,sourceContext,sourceTail,
      right,fieldWord,nxContext,dxContext,nyContext,PA17TMRatArithmeticWidth018.nyStream,
      PA17TMRatArithmeticWidth018.nxStream,List.cons_append,List.nil_append,List.append_nil,List.append_assoc] using hp
  | dx =>
    let tail := (fieldWord (dxContext nyTail dyTail) (false::dxTail) suffix).tail
    have h : BoundedRun PA17TMRatArithmeticWidth018.forwardDxMachine
        (Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx
          (PA17TMRatArithmeticWidth018.nxStream (false::nxTail) (false::tail)))) 9
        (Tape.mk₂ (false::PA17TMRatArithmeticWidth018.dxContext sx counter (false::nxTail)) (false::tail))
        (2*(false::nxTail).length+10) :=
      ⟨PA17TMRatArithmeticWidth018.forwardDxTrace sx counter (false::nxTail) tail,
        PA17TMRatArithmeticWidth018.forwardDx_runsFrom sx counter (false::nxTail) tail,
        by rw [PA17TMRatArithmeticWidth018.forwardDxTrace_length]⟩
    have hp := (bounded_pad (by decide : 9≤16) h).mono
      (by unfold navigationFee; omega : 2*(false::nxTail).length+10≤ navigationFee nxTail dxTail nyTail)
    have hport : padLabel (by decide : 9≤16) (9 : Fin 10)=(9 : Fin 17) := by decide
    rw [hport] at hp
    simpa only [sourceNavigation,sourcePort,sourceHeaderTape,sourceBank,sourceArchive,sourceContext,sourceTail,
      tail,fieldWord,nxContext,PA17TMRatArithmeticWidth018.nxStream,PSTRTMIncrement009.blocks,
      List.flatMap_cons,List.cons_append,List.nil_append,List.append_nil,List.append_assoc,List.tail_cons] using hp
  | nx =>
    let right := sourceBank nxTail dxTail nyTail dyTail suffix
    have h : BoundedRun PA17TMRatArithmeticWidth018.forwardNxMachine
        (Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx right)) 7
        (Tape.mk₂ (PA17TMRatArithmeticWidth018.prefixLeft sx counter) right) 8 :=
      ⟨PA17TMRatArithmeticWidth018.forwardNxTrace sx counter right,
        PA17TMRatArithmeticWidth018.forwardNx_runsFrom sx counter right,by rfl⟩
    have hp := (bounded_pad (by decide : 7≤16) h).mono
      (by unfold navigationFee; omega : 8≤ navigationFee nxTail dxTail nyTail)
    exact hp

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticMul047
