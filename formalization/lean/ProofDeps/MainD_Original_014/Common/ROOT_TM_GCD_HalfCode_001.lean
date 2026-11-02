module
public import Common.PSTR_TM_NativeMul_112
public import Structure.PA17_TM_Division_Sub_001c

set_option autoImplicit false
set_option warningAsError true
@[expose] public section

namespace PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalf001
open PaperProofs.Common.Native.RationalControllerComputation

abbrev carryControl := _root_.PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfCode082.control
abbrev higherBit := _root_.PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfCode082.higher
abbrev seenBit := _root_.PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfCode082.seen
abbrev nextCarry := _root_.PaperProofs.Common.Native.RationalControllerComputation.PSTRTMMulHalfCode082.nextControl

abbrev Pair := Bool × Bool

def readB (r : Fin 4) : Fin 25 := ⟨1 + r.val, by have h := r.isLt; omega⟩
def backward (phase : Fin 4) (r : Fin 4) : Fin 25 :=
  ⟨5 + 4 * phase.val + r.val, by have hp := phase.isLt; have hr := r.isLt; omega⟩
def haltLabel (r : Fin 4) : Fin 25 := ⟨21 + r.val, by have h := r.isLt; omega⟩

/-- Fixed25-label resident high-to-low binary halver for B. It reads actual
four-cell A/flag/B/flag columns, writes B only, and returns across the real
left false guard. The discarded old low bit and actual new-nonzero flag
are in real HALT control. No width, parity, zero-test or fuel input. -/
def halfMachine : Machine 24 := fun q symbol =>
  if h0 : q.val = 0 then some (backward 3 (carryControl false false), .move .left)
  else if h1 : q.val < 5 then
    let r : Fin 4 := ⟨q.val - 1, by omega⟩
    some (backward 0 (nextCarry r symbol), .write (higherBit r))
  else if h2 : q.val < 21 then
    let r : Fin 4 := ⟨(q.val - 5) % 4, Nat.mod_lt _ (by decide)⟩
    if q.val < 17 then some (⟨q.val + 4, by omega⟩, .move .left)
    else if symbol then some (readB r, .move .left)
    else some (haltLabel r, .move .right)
  else none

def state (q : Fin 25) (left right : List Bool) : MachineState 24 :=
  ⟨q, Turing.Tape.mk₂ left right⟩

def resultReverse : Fin 4 → List Pair → List Pair
  | _, [] => []
  | r, (a,b) :: earlier => (a, higherBit r) :: resultReverse (nextCarry r b) earlier

def finalControl : Fin 4 → List Pair → Fin 4
  | r, [] => r
  | r, (_,b) :: earlier => finalControl (nextCarry r b) earlier

def halfPairs (pairs : List Pair) : List Pair :=
  (resultReverse (carryControl false false) pairs.reverse).reverse

theorem half_halt (r : Fin 4) (left right : List Bool) :
    Turing.TM0.step halfMachine (state (haltLabel r) left right) = none := by
  have hr := r.isLt
  simp [Turing.TM0.step, halfMachine, state, haltLabel,
    show ¬21 + r.val < 5 by omega,
    show ¬21 + r.val < 21 by omega]

end PaperProofs.Common.Native.RationalControllerComputation.ROOTTMGCDHalf001
