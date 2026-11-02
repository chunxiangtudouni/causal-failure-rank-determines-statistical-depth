module
public import Structure.PA17_TM_RatArithmetic_FarLoad_031h

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
open Turing PA17TMDivisionCompose006
open PA17TMRatArithmeticWidth018 (BoundedRun)

inductive SourceField where
  | dy | ny | dx | nx

def sourceNavigation : SourceField → Machine 16
  | .dy => PA17TMRatArithmeticWidth018.forwardDyMachine
  | .ny => padMachine (by decide) PA17TMRatArithmeticWidth018.forwardNyMachine
  | .dx => padMachine (by decide) PA17TMRatArithmeticWidth018.forwardDxMachine
  | .nx => padMachine (by decide) PA17TMRatArithmeticWidth018.forwardNxMachine

def sourceRoute : SourceField → FarRoute
  | .dy => dyRoute | .ny => nyRoute | .dx => dxRoute | .nx => nxRoute
def sourceSlot : SourceField → Nat
  | .dy => 0 | .ny => 1 | .dx => 3 | .nx => 4
def sourcePort : SourceField → Fin 17
  | .dy => 16 | .ny => 14 | .dx => 9 | .nx => 7

def sourceContext (field : SourceField) (dxTail nyTail dyTail : List Bool) : List Bool :=
  match field with
  | .dy => [] | .ny => nyContext dyTail | .dx => dxContext nyTail dyTail
  | .nx => nxContext dxTail nyTail dyTail
def sourceFinish (field : SourceField) (dxTail nyTail dyTail : List Bool) :
    List Bool → List Bool → List Bool :=
  match field with
  | .dy => dyFinish | .ny => nyFinish dyTail | .dx => dxFinish nyTail dyTail
  | .nx => nxFinish dxTail nyTail dyTail
def sourceCost (field : SourceField) (dxTail nyTail dyTail : List Bool) : Nat :=
  match field with
  | .dy => 5 | .ny => 2*(false::dyTail).length+10
  | .dx => 2*((false::nyTail).length+(false::dyTail).length)+18
  | .nx => 2*((false::dxTail).length+(false::nyTail).length+(false::dyTail).length)+23
def sourceTail (field : SourceField) (nxTail dxTail nyTail dyTail : List Bool) : List Bool :=
  match field with | .dy => dyTail | .ny => nyTail | .dx => dxTail | .nx => nxTail
def sourceArchive (field : SourceField) (sx : Bool) (counter nxTail dxTail nyTail : List Bool) : List Bool :=
  match field with
  | .dy => PA17TMRatArithmeticWidth018.dyContext sx counter (false::nxTail) (false::dxTail) (false::nyTail)
  | .ny => PA17TMRatArithmeticWidth018.nyContext sx counter (false::nxTail) (false::dxTail)
  | .dx => PA17TMRatArithmeticWidth018.dxContext sx counter (false::nxTail)
  | .nx => PA17TMRatArithmeticWidth018.nxContext sx counter

def sourceBank (nxTail dxTail nyTail dyTail suffix : List Bool) : List Bool :=
  fieldWord (nxContext dxTail nyTail dyTail) (false::nxTail) suffix
def headerTape (sx : Bool) (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) : Tape Bool :=
  Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx
    (sourceBank nxTail dxTail nyTail dyTail (workSuffix gap [])))
def navigationFee (nxTail dxTail nyTail : List Bool) : Nat :=
  2*((false::nxTail).length+(false::dxTail).length+(false::nyTail).length)+17

theorem source_correct (field : SourceField) (dxTail nyTail dyTail : List Bool) :
    RouteCorrect (sourceRoute field) (sourceContext field dxTail nyTail dyTail)
      (sourceFinish field dxTail nyTail dyTail) (sourceCost field dxTail nyTail dyTail) := by
  cases field
  · exact dy_route_correct
  · exact ny_route_correct dyTail
  · exact dx_route_correct nyTail dyTail
  · exact nx_route_correct dxTail nyTail dyTail

/-- All four paths start at the real original header. Neither a source
head, source width, nor a global-footer jump is supplied by the caller. -/
theorem source_navigation_bounded (field : SourceField) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap : Nat) :
    BoundedRun (sourceNavigation field) (headerTape sx counter nxTail dxTail nyTail dyTail gap)
      (sourcePort field)
      (Tape.mk₂ (false::sourceArchive field sx counter nxTail dxTail nyTail)
        (fieldWord (sourceContext field dxTail nyTail dyTail)
          (false::sourceTail field nxTail dxTail nyTail dyTail) (workSuffix gap [])))
      (navigationFee nxTail dxTail nyTail) := by
  cases field with
  | dy =>
    let tail := (fieldWord [] (false::dyTail) (workSuffix gap [])).tail
    have h : BoundedRun PA17TMRatArithmeticWidth018.forwardDyMachine
        (Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx
          (PA17TMRatArithmeticWidth018.dyStream (false::nxTail) (false::dxTail) (false::nyTail) (false::tail)))) 16
        (Tape.mk₂ (false::PA17TMRatArithmeticWidth018.dyContext sx counter (false::nxTail)
          (false::dxTail) (false::nyTail)) (false::tail))
        (2*((false::nxTail).length+(false::dxTail).length+(false::nyTail).length)+17) :=
      ⟨PA17TMRatArithmeticWidth018.forwardDyTrace sx counter (false::nxTail) dxTail (false::nyTail) tail,
        PA17TMRatArithmeticWidth018.forwardDy_runsFrom sx counter (false::nxTail) dxTail (false::nyTail) tail,
        by rw [PA17TMRatArithmeticWidth018.forwardDyTrace_length]⟩
    simpa only [sourceNavigation,sourcePort,headerTape,sourceBank,sourceArchive,sourceContext,sourceTail,
      navigationFee,tail,fieldWord,nxContext,dxContext,PA17TMRatArithmeticWidth018.dyStream,
      PA17TMRatArithmeticWidth018.nyStream,PA17TMRatArithmeticWidth018.nxStream,
      PSTRTMIncrement009.blocks,List.flatMap_cons,List.cons_append,List.nil_append,List.append_nil,
      List.append_assoc,List.tail_cons] using h
  | ny =>
    let right := fieldWord (nyContext dyTail) (false::nyTail) (workSuffix gap [])
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
    simpa only [sourceNavigation,sourcePort,headerTape,sourceBank,sourceArchive,sourceContext,sourceTail,
      right,fieldWord,nxContext,dxContext,nyContext,PA17TMRatArithmeticWidth018.nyStream,
      PA17TMRatArithmeticWidth018.nxStream,List.cons_append,List.nil_append,List.append_nil,List.append_assoc] using hp
  | dx =>
    let tail := (fieldWord (dxContext nyTail dyTail) (false::dxTail) (workSuffix gap [])).tail
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
    simpa only [sourceNavigation,sourcePort,headerTape,sourceBank,sourceArchive,sourceContext,sourceTail,
      tail,fieldWord,nxContext,PA17TMRatArithmeticWidth018.nxStream,PSTRTMIncrement009.blocks,
      List.flatMap_cons,List.cons_append,List.nil_append,List.append_nil,List.append_assoc,List.tail_cons] using hp
  | nx =>
    let right := sourceBank nxTail dxTail nyTail dyTail (workSuffix gap [])
    have h : BoundedRun PA17TMRatArithmeticWidth018.forwardNxMachine
        (Tape.mk₂ counter (PA17TMRatArithmeticWidth018.prefixRight sx right)) 7
        (Tape.mk₂ (PA17TMRatArithmeticWidth018.prefixLeft sx counter) right) 8 :=
      ⟨PA17TMRatArithmeticWidth018.forwardNxTrace sx counter right,
        PA17TMRatArithmeticWidth018.forwardNx_runsFrom sx counter right,by rfl⟩
    have hp := (bounded_pad (by decide : 7≤16) h).mono
      (by unfold navigationFee; omega : 8≤ navigationFee nxTail dxTail nyTail)
    exact hp

def originalLoader (p : Nat) (field : SourceField) : Machine (totalStates p 435) :=
  restoreMachine p (sourceSlot field) (sourceNavigation field) (sourceRoute field)

/-- Incoming memory32/64 is retained. The only restored payload cell is
the DEST first DATA, using the actual row's saved bit. Source DATA stays0. -/
theorem original_loader_contract (p : Nat) (field : SourceField) (memory : Fin (p+1)) (sx : Bool)
    (counter nxTail dxTail nyTail dyTail : List Bool) (gap inputLength : Nat) :
    ∃ trace, PSTRTMSeq005.RunsFrom (originalLoader p field)
      (blockCfg memory (⟨0,headerTape sx counter nxTail dxTail nyTail dyTail gap⟩ : MachineState 435)) trace
      (blockCfg memory (⟨435,Tape.mk₂
        (destinationLeft gap (sourceFinish field dxTail nyTail dyTail
          (false::sourceArchive field sx counter nxTail dxTail nyTail)
          (false::sourceTail field nxTail dxTail nyTail dyTail)))
        (PA17TMRatArithmeticCopy006.workspace
          (memory.val.testBit (sourceSlot field)::sourceTail field nxTail dxTail nyTail dyTail))⟩ : MachineState 435)) ∧
      trace.length≤ navigationFee nxTail dxTail nyTail+
        copyFee (false::sourceTail field nxTail dxTail nyTail dyTail) (sourceCost field dxTail nyTail dyTail) gap+2 ∧
      ∀ k, visitedSpace (originalLoader p field) inputLength (trace.take k) ≤ inputLength+2*
        (navigationFee nxTail dxTail nyTail+
          copyFee (false::sourceTail field nxTail dxTail nyTail dyTail) (sourceCost field dxTail nyTail dyTail) gap+2)+1 :=
  restore_contract p (sourceSlot field) (sourceNavigation field) (sourceRoute field) _ _ _
    (source_correct field dxTail nyTail dyTail) memory _ (sourcePort field) _ _ _ gap inputLength
    (source_navigation_bounded field sx counter nxTail dxTail nyTail dyTail gap)

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticFarLoad031
