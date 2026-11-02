module
public import Structure.PA17_TM_RatArithmetic_Width_018i

attribute [local implicit_reducible] PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionCompose006.totalStates
@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
open PA17TMDivisionCompose006

def savedPhase (memory : Fin 32) : Fin 33 := ⟨memory.val+1,by have h:=memory.isLt;omega⟩
def decodeObserved (q : Fin 2402) : Fin 32 := ⟨((q.val-2210)/6)%32,Nat.mod_lt _ (by decide)⟩

def widthFamily (phase : Fin 33) : Machine 2401 :=
  if phase.val=0 then PA17TMRatArithmeticBookmark014.rawBookmarkMachine
  else padMachine (by decide : 645≤2401) middleMachine
def widthPorts (phase : Fin 33) (q : Fin 2402) : Option (Fin 33 × Fin 2402) :=
  if phase.val=0 then some (savedPhase (decodeObserved q),0) else none

/-- Fixed original-input parser/bookmarker plus 32 copies of the same
width program. An actual raw HALT label selects its saved memory copy by
a paid write-self transfer. No bit tuple or width is a program input. -/
def widthMachine : Machine 79265 := blockMachine widthFamily widthPorts
def widthEntry (memory : Fin 32) (tape : Turing.Tape Bool) : MachineState 79265 :=
  blockCfg (s:=2401) (savedPhase memory) ⟨0,tape⟩
def widthFinal (memory : Fin 32) (tape : Turing.Tape Bool) : MachineState 79265 :=
  blockCfg (s:=2401) (savedPhase memory) ⟨645,tape⟩

theorem widthFamily_saved (memory : Fin 32) :
    widthFamily (savedPhase memory)=padMachine (by decide : 645≤2401) middleMachine := by
  simp [widthFamily,savedPhase]

theorem widthFinal_label (memory : Fin 32) (tape : Turing.Tape Bool) :
    (widthFinal memory tape).q.val=(memory.val+1)*2402+645 := rfl

/-- Internal memory-preserving refill entry. The saved memory parameter
describes an already observed control label, not additional original
input. The caller physically enters Nx with the left unary counter empty
or at n; no parser, tape reset, workspace scan or free copy is hidden here. -/
theorem middle_memory_runs (memory : Fin 32) (sx : Bool) (n : Nat)
    (nxTail dxTail nyTail dyTail suffix : List Bool) :
    ∃ trace, PSTRTMSeq005.RunsFrom widthMachine
      (widthEntry memory (Turing.Tape.mk₂ (false::nxContext sx (false::ROOTTMGCDCounter011.ones n))
        (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) suffix))) trace
      (widthFinal memory (Turing.Tape.mk₂
        (false::ROOTTMGCDCounter011.ones (n+bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)))
        (prefixRight sx (bank (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail) suffix)))) ∧
      trace.length≤bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)*
        (2*n+6*bankWidth (false::nxTail) (false::dxTail) (false::nyTail) (false::dyTail)+68)+48 := by
  obtain ⟨localTrace,hr,hl⟩ := middle_bounded sx n nxTail dxTail nyTail dyTail suffix
  have hp := pad_runsFrom (by decide : 645≤2401) middleMachine _ _ _ hr
  have hf := hp
  rw [←widthFamily_saved memory] at hf
  have hs := block_segment widthFamily widthPorts (savedPhase memory) _ _ _ hf
  refine ⟨(localTrace.map (padCfg (by decide : 645≤2401))).map (blockCfg (savedPhase memory)),?_,?_⟩
  · refine ⟨hs.1,hs.2.1,hs.2.2,?_⟩
    apply block_halt widthFamily widthPorts (savedPhase memory) _ hf.2.2.2
    simp [widthPorts,savedPhase]
  · simpa only [List.length_map] using hl

theorem decodeObserved_actual (x y : Rat) :
    decodeObserved (PA17TMRatArithmeticBookmark014.rawBookmarkFinal x y).q=
      PA17TMRatArithmeticBookmark014.mNx x y := by
  apply Fin.ext
  change (((PA17TMRatArithmeticBookmark014.rawBookmarkFinal x y).q.val-2210)/6)%32 = _
  rw [PA17TMRatArithmeticBookmark014.rawBookmark_final_label]
  have h := (PA17TMRatArithmeticBookmark014.mNx x y).isLt
  omega

theorem raw_memory_transfer (x y : Rat) :
    Turing.TM0.step widthMachine
      (blockCfg (0 : Fin 33) (PA17TMRatArithmeticBookmark014.rawBookmarkFinal x y)) =
      some (widthEntry (PA17TMRatArithmeticBookmark014.mNx x y)
        (PA17TMRatArithmeticBookmark014.rawBookmarkFinal x y).Tape) := by
  have hr := PA17TMRatArithmeticBookmark014.rawBookmark_runs x y
  apply block_transfer widthFamily widthPorts (0 : Fin 33)
    (PA17TMRatArithmeticBookmark014.rawBookmarkFinal x y)
    (savedPhase (PA17TMRatArithmeticBookmark014.mNx x y),0) hr.2.2.2.1
  simp only [widthPorts,Fin.val_zero,ite_true,decodeObserved_actual]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticWidth018
