module
public import Common.PSTR_TM_ColumnRewind_067

/-! Actual rawPack-to-division initialization. The archive is four-cell
[source,1,pending=1,1], separated from resident R/B by three false cells. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
open PSTRTMBinaryAdd024
open PSTRTMCompareCode054 (leftColumns)

def archivePairs (pairs : List (Bool × Bool)) : List (Bool × Bool) := pairs.map (fun pair => (pair.1,true))
def residentPairs (pairs : List (Bool × Bool)) : List (Bool × Bool) := pairs.map (fun pair => (false,pair.2))
def markedColumns (pairs : List (Bool × Bool)) : List Bool := pairs.flatMap (fun pair => [false,false,pair.2,true])
def archiveLeft (pairs : List (Bool × Bool)) : List Bool := leftColumns (archivePairs pairs).reverse
def sep (archive : List Bool) : List Bool := false :: false :: false :: archive

def keep (phase : Fin 20) (a : Bool) : Fin 67 :=
  ⟨10 + 2 * phase.val + a.toNat, by have hp := phase.isLt; have ha := Bool.toNat_le a; omega⟩

/-- Exactly67 fixed labels. All loops are actual flag/sentinel scans; a source
bit is held in two finite-control lanes while the real tape is copied. -/
def prefixMachine : Machine 66 := fun q symbol =>
  if q.val < 10 then
    match q.val with
    | 0 => some (1, .move .right)
    | 1 => if symbol then some (2, .move .right) else some (5, .move .left)
    | 2 => some (3, .move .right)
    | 3 => some (0, .move .right)
    | 5 => some (6, .move .left)
    | 6 => if symbol then some (7, .move .left) else some (60, .move .right)
    | 7 => some (8, .move .left)
    | 8 => some (9, .move .left)
    | 9 => some (keep 0 symbol, .write false)
    | _ => none
  else if q.val < 50 then
    let a := decide (q.val % 2 = 1)
    match (q.val - 10) / 2 with
    | 0 => some (keep 1 a, .move .right)
    | 1 => some (keep 2 a, .write false)
    | 2 => some (keep 3 a, .move .left)
    | 3 => some (keep 4 a, .move .left)
    | 4 => if symbol then some (keep 5 a, .move .left) else some (keep 8 a, .move .left)
    | 5 => some (keep 6 a, .move .left)
    | 6 => some (keep 7 a, .move .left)
    | 7 => some (keep 4 a, .move .left)
    | 8 => some (keep 9 a, .move .left)
    | 9 => some (keep 10 a, .move .left)
    | 10 => if symbol then some (keep 11 a, .move .left) else some (keep 14 a, .write true)
    | 11 => some (keep 12 a, .move .left)
    | 12 => some (keep 13 a, .move .left)
    | 13 => some (keep 10 a, .move .left)
    | 14 => some (keep 15 a, .move .left)
    | 15 => some (keep 16 a, .write true)
    | 16 => some (keep 17 a, .move .left)
    | 17 => some (keep 18 a, .write true)
    | 18 => some (keep 19 a, .move .left)
    | _ => some (50, .write a)
  else
    match q.val with
    | 50 => some (51, .move .right)
    | 51 => if symbol then some (52, .move .right) else some (56, .move .right)
    | 52 => some (53, .move .right)
    | 53 => some (54, .move .right)
    | 54 => some (51, .move .right)
    | 56 => some (0, .move .right)
    | 60 => some (61, .move .right)
    | 61 => some (62, .write true)
    | 62 => some (63, .move .right)
    | 63 => some (64, .move .right)
    | 64 => if symbol then some (60, .move .right) else some (65, .write true)
    | 65 => some (66, .move .right)
    | _ => none

def state (q : Fin 67) (left right : List Bool) : MachineState 66 := ⟨q, Turing.Tape.mk₂ left right⟩

def Segment (first : MachineState 66) (trace : List (MachineState 66)) (last : MachineState 66) : Prop :=
  trace.head? = some first ∧ trace.IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) ∧ trace.getLast? = some last

def splice (first second : List (MachineState 66)) : List (MachineState 66) := first.dropLast ++ second

theorem segment_single (s : MachineState 66) : Segment s [s] s := by
  exact ⟨rfl, List.IsChain.singleton _, rfl⟩

theorem segment_splice {first middle last : MachineState 66} {xs ys : List (MachineState 66)}
    (hx : Segment first xs middle) (hy : Segment middle ys last) : Segment first (splice xs ys) last := by
  have ex : xs.dropLast ++ [middle] = xs := List.dropLast_append_getLast? middle hx.2.2
  have ey : middle :: ys.tail = ys := List.cons_head?_tail hy.1
  refine ⟨?_, ?_, ?_⟩
  · cases xs with
    | nil => simp [Segment] at hx
    | cons a later =>
      cases later with
      | nil =>
        have ha : a = first := Option.some.inj hx.1
        have hm : a = middle := Option.some.inj hx.2.2
        simpa only [splice, List.dropLast_singleton, List.nil_append, ← ha, hm] using hy.1
      | cons b later => simpa only [splice, List.dropLast_cons_cons, List.cons_append, List.head?_cons] using hx.1
  · have cx : (xs.dropLast ++ [middle]).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := ex.symm ▸ hx.2.1
    have cy : ([middle] ++ ys.tail).IsChain (fun before after => Turing.TM0.step prefixMachine before = some after) := by
      simpa only [List.singleton_append, ey] using hy.2.1
    have joined := cx.append_overlap cy (by simp)
    simpa only [splice, List.append_assoc, List.singleton_append, ey] using joined
  · simp only [splice, List.getLast?_append, hy.2.2, Option.some_or]

theorem splice_length {first middle : MachineState 66} {xs : List (MachineState 66)}
    (hx : Segment first xs middle) (ys : List (MachineState 66)) :
    (splice xs ys).length + 1 = xs.length + ys.length := by
  have hn : xs ≠ [] := by intro he; simp [Segment,he] at hx
  simp only [splice, List.length_append, List.length_dropLast]
  have hp := List.length_pos_iff.mpr hn
  omega

theorem prefix_halt (left right : List Bool) : Turing.TM0.step prefixMachine (state 66 left right) = none := by
  simp [Turing.TM0.step, prefixMachine, state]

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMDivisionInit004
