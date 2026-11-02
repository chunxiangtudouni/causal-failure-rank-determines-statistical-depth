module
public import Paid.PDCompute_Pack_InitializeLayout_019
public import Paid.PDCompute_Pack_PointerHeader_020

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver

def counterFirst (before : State) (base n : ℕ) : State := copyPlusOneResult before base 3 rowRemaining n
def counterSecond (before : State) (base n k : ℕ) : State :=
  copyPlusOneResult (counterFirst before base n) base 4 columnsPerRow k
def headerArithmetic (before : State) (base n k : ℕ) : State := pointerArithmeticResult (counterSecond before base n k) base n k
def initializeHeaderResult (before : State) (base n k : ℕ) : State := pointerStoresResult (headerArithmetic before base n k) base

def counterValues (values : ℕ → Cell) (n k : ℕ) : ℕ → Cell :=
  Function.update (Function.update values rowRemaining (.natural (n+1))) columnsPerRow (.natural (k+1))
def initializeHeaderValues (values : ℕ → Cell) (base n k : ℕ) : ℕ → Cell :=
  pointerValues (counterValues values n k) base (resultBase base n k)

theorem counterFirst_header (before : State) (base n : ℕ) (values : ℕ → Cell) (header : Header before base values) :
    Header (counterFirst before base n) base (Function.update values rowRemaining (.natural (n+1))) :=
  copyPlusOne_header before base 3 rowRemaining n values header (by decide)

theorem counterSecond_header (before : State) (base n k : ℕ) (values : ℕ → Cell) (header : Header before base values) :
    Header (counterSecond before base n k) base (counterValues values n k) :=
  copyPlusOne_header (counterFirst before base n) base 4 columnsPerRow k _
    (counterFirst_header before base n values header) (by decide)

theorem headerArithmetic_header (before : State) (base n k : ℕ) (values : ℕ → Cell) (header : Header before base values) :
    Header (headerArithmetic before base n k) base (counterValues values n k) :=
  pointerArithmetic_header (counterSecond before base n k) base n k _ (counterSecond_header before base n k values header)

theorem initializeHeader_header (before : State) (base n k : ℕ) (values : ℕ → Cell) (header : Header before base values) :
    Header (initializeHeaderResult before base n k) base (initializeHeaderValues values base n k) :=
  pointerStores_header (headerArithmetic before base n k) base (resultBase base n k) _
    (headerArithmetic_header before base n k values header)
    (pointerArithmetic_fields (counterSecond before base n k) base n k).2.2.2.2.1

theorem initializeHeaderValues_arguments (values : ℕ → Cell) (base n k slot : ℕ) (inside : slot<6) :
    initializeHeaderValues values base n k slot=values slot := by
  have h40 : slot≠40 := by omega
  have h42 : slot≠42 := by omega
  have h43 : slot≠43 := by omega
  have h44 : slot≠44 := by omega
  have h47 : slot≠47 := by omega
  simp [initializeHeaderValues,counterValues,pointerValues,rowRemaining,columnsPerRow,sourceCursor,
    outputStart,outputCursor,h40,h42,h43,h44,h47]

theorem counterValues_rows (values : ℕ → Cell) (n k : ℕ) : counterValues values n k rowRemaining=.natural (n+1) := by
  simp [counterValues,rowRemaining,columnsPerRow]
theorem counterValues_columns (values : ℕ → Cell) (n k : ℕ) : counterValues values n k columnsPerRow=.natural (k+1) := by
  simp [counterValues]

end PDCompute.Pack
