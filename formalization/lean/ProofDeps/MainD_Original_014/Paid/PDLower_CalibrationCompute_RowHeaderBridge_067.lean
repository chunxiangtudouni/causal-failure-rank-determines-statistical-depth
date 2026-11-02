module

public import Paid.PDLower_CalibrationCompute_HeaderOps_027
public import Paid.PDROC_CalibrationRow_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- Convert the caller's actual sixteen-cell header to the frozen row
routine's original physical argument structure. No row or run is input. -/
theorem Header.At.rowArguments {P : Parameters} {before : State} {base : ℕ} {header : Header}
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (M : header.M=P.certificate.M) (Q : header.Q=P.certificate.Q)
    (gamma : header.gamma=P.certificate.gamma) :
    PDROC.CalibrationRow.Header P base header.level before := by
  refine ⟨fresh,?_,?_,?_,?_,?_,?_,?_⟩
  · intro offset inside
    exact represented.1 offset (by simpa only [Header.cells_length] using inside)
  · simpa only [M] using (represented.lookup (offset:=2) (value:=.natural header.M) rfl).1
  · simpa only [Q] using (represented.lookup (offset:=3) (value:=.natural header.Q) rfl).1
  · simpa only [gamma] using (represented.lookup (offset:=4) (value:=.rational header.gamma) rfl).1
  · exact (represented.lookup (offset:=5) (value:=.natural header.level) rfl).1
  · simpa only [gamma] using
      (represented.lookup (offset:=12) (value:=.rational (1/2-header.gamma)) rfl).1
  · simpa only [gamma] using
      (represented.lookup (offset:=13) (value:=.rational (1/2+header.gamma)) rfl).1

/-- Recover ALL caller fields after the row routine from its real five
mutable header words and its original strong frame. ReturnPC, endpoint
cache, q, output cursor and padding are preserved physically. -/
theorem Header.At.afterRow {before after : State} {base : ℕ} {header : Header}
    (represented : header.At before base)
    (frame : MemoryFrame (PDROC.CalibrationRow.region base header.M) before after)
    (live : ∀ offset<16,base+offset∈after.live)
    (clock cursor width read write : ℕ)
    (hclock : after.heap (base+6)=.natural clock)
    (hcursor : after.heap (base+7)=.natural cursor)
    (hwidth : after.heap (base+8)=.natural width)
    (hread : after.heap (base+9)=.natural read)
    (hwrite : after.heap (base+10)=.natural write) :
    ({header with clock:=clock,cursor:=cursor,width:=width,readBase:=read,writeBase:=write}).At after base := by
  have preserved (offset : ℕ) (inside : offset<16) (outside : offset<6 ∨ 10<offset)
      (value : Cell) (lookup : header.cells[offset]?=some value) : after.heap (base+offset)=value :=
    (frame.1 _ (PDROC.CalibrationRow.header_outside base header.M offset inside outside)).trans
      (represented.lookup lookup).1
  apply HeapList.of_values
  · intro offset inside
    exact live offset (by simpa only [Header.cells_length] using inside)
  · intro offset inside
    have bounded : offset<16 := by simpa only [Header.cells_length] using inside
    interval_cases offset
    · exact preserved 0 (by decide) (by decide) (.natural header.returnPC) rfl
    · exact preserved 1 (by decide) (by decide) (.natural header.endpoints) rfl
    · exact preserved 2 (by decide) (by decide) (.natural header.M) rfl
    · exact preserved 3 (by decide) (by decide) (.natural header.Q) rfl
    · exact preserved 4 (by decide) (by decide) (.rational header.gamma) rfl
    · exact preserved 5 (by decide) (by decide) (.natural header.level) rfl
    · exact hclock
    · exact hcursor
    · exact hwidth
    · exact hread
    · exact hwrite
    · exact preserved 11 (by decide) (by decide) (.rational header.q) rfl
    · exact preserved 12 (by decide) (by decide) (.rational (1/2-header.gamma)) rfl
    · exact preserved 13 (by decide) (by decide) (.rational (1/2+header.gamma)) rfl
    · exact preserved 14 (by decide) (by decide) (.natural 0) rfl
    · exact preserved 15 (by decide) (by decide) (.natural header.outputCursor) rfl

end PDLower.CalibrationCompute
