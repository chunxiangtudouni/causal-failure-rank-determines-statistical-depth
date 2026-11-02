module
public import Paid.PDCompute_Pack_InitializeModel_022
public import Paid.PDCompute_Pack_PrefixJoin_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver
open PDLower.CalibrationCompute (linearExecute linearExecute_append)

theorem copyPlusOne_fresh (before : State) (base source target value : ℕ) :
    (copyPlusOneResult before base source target value).register .fresh=before.register .fresh :=
  (addNatSlotResult_fields (copySlotResult before base source target) base target value 1).2.2.1.trans
    (copySlotResult_fields before base source target).2.2.1

/-- The real first51 literal instructions succeed on the saved original
n/k and have their exact Header48 footprint at every successful prefix.
The calculated result address is not supplied by the caller. -/
theorem initializeHeader_run_memory (input : List Cell) (before : State) (base n k : ℕ)
    (values : ℕ → Cell) (header : Header before base values)
    (hbase : before.register .fresh=.natural base) (hn : values 3=.natural n) (hk : values 4=.natural k) :
    linearExecute input initializeHeaderCode before=some (initializeHeaderResult before base n k) ∧
    ∀ count ≤ initializeHeaderCode.length,∀ after,
      linearExecute input (initializeHeaderCode.take count) before=some after → HeaderMemory before after base := by
  let values1:=Function.update values rowRemaining (.natural (n+1))
  let values2:=counterValues values n k
  have head1 : Header (counterFirst before base n) base values1 := counterFirst_header before base n values header
  have head2 : Header (counterSecond before base n k) base values2 := counterSecond_header before base n k values header
  have head3 : Header (headerArithmetic before base n k) base values2 := headerArithmetic_header before base n k values header
  have base1 : (counterFirst before base n).register .fresh=.natural base :=
    (copyPlusOne_fresh before base 3 rowRemaining n).trans hbase
  have base2 : (counterSecond before base n k).register .fresh=.natural base :=
    (copyPlusOne_fresh (counterFirst before base n) base 4 columnsPerRow k).trans base1
  have base3 : (headerArithmetic before base n k).register .fresh=.natural base :=
    (pointerArithmetic_fields (counterSecond before base n k) base n k).2.2.2.1.trans base2
  have value4 : values1 4=.natural k := by simpa [values1,rowRemaining] using hk
  have run1 : linearExecute input (copyPlusOneCode 3 rowRemaining) before=some (counterFirst before base n) :=
    copyPlusOne_execute input before base 3 rowRemaining n values header (by decide) hbase hn
  have run2 : linearExecute input (copyPlusOneCode 4 columnsPerRow) (counterFirst before base n)=
      some (counterSecond before base n k) :=
    copyPlusOne_execute input (counterFirst before base n) base 4 columnsPerRow k values1 head1 (by decide) base1 value4
  have run3 : linearExecute input pointerArithmeticCode (counterSecond before base n k)=
      some (headerArithmetic before base n k) :=
    pointerArithmetic_execute input (counterSecond before base n k) base n k values2 head2 base2
      (counterValues_rows values n k) (counterValues_columns values n k)
  have run4 : linearExecute input pointerStoresCode (headerArithmetic before base n k)=
      some (initializeHeaderResult before base n k) :=
    pointerStores_execute input (headerArithmetic before base n k) base base3
  constructor
  · simp only [initializeHeaderCode,List.append_assoc,linearExecute_append,run1,Option.bind_some,run2,run3,run4]
  · have mem1 : ∀ count≤(copyPlusOneCode 3 rowRemaining).length,∀ state,
        linearExecute input ((copyPlusOneCode 3 rowRemaining).take count) before=some state → HeaderMemory before state base := by
      intro count bound state execute
      exact copyPlusOne_prefix_memory input before state base 3 rowRemaining n values header
        (by decide) (by decide) hbase hn count bound execute
    have mem2 : ∀ count≤(copyPlusOneCode 4 columnsPerRow).length,∀ state,
        linearExecute input ((copyPlusOneCode 4 columnsPerRow).take count) (counterFirst before base n)=some state →
          HeaderMemory (counterFirst before base n) state base := by
      intro count bound state execute
      exact copyPlusOne_prefix_memory input (counterFirst before base n) state base 4 columnsPerRow k values1 head1
        (by decide) (by decide) base1 value4 count bound execute
    have mem3 : ∀ count≤pointerArithmeticCode.length,∀ state,
        linearExecute input (pointerArithmeticCode.take count) (counterSecond before base n k)=some state →
          HeaderMemory (counterSecond before base n k) state base := by
      intro count _bound state execute
      exact pointerArithmetic_prefix_memory input (counterSecond before base n k) state base count execute
    have mem4 : ∀ count≤pointerStoresCode.length,∀ state,
        linearExecute input (pointerStoresCode.take count) (headerArithmetic before base n k)=some state →
          HeaderMemory (headerArithmetic before base n k) state base := by
      intro count bound state execute
      exact pointerStores_prefix_memory input (headerArithmetic before base n k) state base values2 head3 base3 count bound execute
    have tail:=header_prefix_append input pointerArithmeticCode pointerStoresCode (counterSecond before base n k)
      (headerArithmetic before base n k) base run3 mem3 mem4
    have middle:=header_prefix_append input (copyPlusOneCode 4 columnsPerRow) (pointerArithmeticCode++pointerStoresCode)
      (counterFirst before base n) (counterSecond before base n k) base run2 mem2 tail
    have joined:=header_prefix_append input (copyPlusOneCode 3 rowRemaining)
      (copyPlusOneCode 4 columnsPerRow++(pointerArithmeticCode++pointerStoresCode)) before (counterFirst before base n) base run1 mem1 middle
    simpa only [initializeHeaderCode,List.append_assoc] using joined

end PDCompute.Pack
