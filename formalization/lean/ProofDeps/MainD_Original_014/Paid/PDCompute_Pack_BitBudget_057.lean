module
public import Paid.RootD27Bits_SlotPrefix_004
public import Paid.PDCompute_Pack_NaturalCap_054
public import Paid.PDCompute_Pack_PeakCells_053

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

noncomputable def initialBits (before : State) : ℕ:=peakOperandBits [before]
noncomputable def serializerBudget (before : State) (n k origin : ℕ) : ℕ:=
  initialBits before+natBits n+natBits k+natBits origin+16

theorem initialBits_safe (before : State) : SafeBits before (initialBits before) := by
  intro bits member
  have nonempty : stateCellBits before≠[] := by
    intro empty
    have lengths:=congrArg List.length empty
    simp only [stateCellBits,List.length_append,List.length_cons,List.length_nil] at lengths
    omega
  unfold initialBits peakOperandBits
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
  rw [List.foldl_max_eq_max nonempty]
  exact (List.le_max_of_mem member).trans (le_max_right _ _)

theorem safeBits_mono {state : State} {first later : ℕ} (safe : SafeBits state first) (bound : first ≤ later) :
    SafeBits state later:=fun bits member=>(safe bits member).trans bound

theorem serializerBudget_initial (before : State) (n k origin : ℕ) :
    SafeBits before (serializerBudget before n k origin) :=
  safeBits_mono (initialBits_safe before) (by unfold serializerBudget;omega)

theorem serializerBudget_natural (before : State) (base n k origin value : ℕ)
    (fresh : before.register .fresh=.natural base) (bound : value ≤ naturalCap base n k) :
    (.natural value : Cell).bits ≤ serializerBudget before n k origin := by
  have initial:=(initialBits_safe before).register .fresh
  rw [fresh] at initial
  have numeric:=naturalCap_bits base n k value bound
  change 1+natBits base ≤ initialBits before at initial
  change 1+natBits value ≤ initialBits before+natBits n+natBits k+natBits origin+16
  omega

theorem serializerBudget_pc (before : State) (n k origin counter : ℕ) (bound : counter ≤ origin+233) :
    natBits counter ≤ serializerBudget before n k origin := by
  have numeric:=origin_pc_bits origin counter bound
  unfold serializerBudget
  omega

theorem serializerBudget_return (before : State) (base returnPC n k origin : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (saved : values 1=.natural returnPC) :
    natBits returnPC ≤ serializerBudget before n k origin := by
  have represented:=(header.value 1 (by decide)).trans saved
  have initial:=(initialBits_safe before).heap (base+1) (header.live 1 (by decide))
  rw [represented] at initial
  change 1+natBits returnPC ≤ initialBits before at initial
  unfold serializerBudget
  omega

theorem header_values_safe {state : State} {base budget : ℕ} {values : ℕ → Cell}
    (safe : SafeBits state budget) (header : Header state base values) (slot : ℕ) (inside : slot<headerWords) :
    (values slot).bits ≤ budget := by
  rw [←header.value slot inside]
  exact safe.heap (base+slot) (header.live slot inside)

theorem dense_values_safe {state : State} {pointer budget : ℕ} {cells : List Cell}
    (safe : SafeBits state budget) (heap : HeapList state pointer cells) (offset : ℕ) (inside : offset<cells.length) :
    cells[offset].bits ≤ budget := by
  rw [←heap.value offset inside]
  exact safe.heap (pointer+offset) (heap.1 offset inside)

theorem safeBits_peak (trace : List State) (budget : ℕ) (safe : ∀ state∈trace,SafeBits state budget) :
    peakOperandBits trace ≤ budget := by
  apply foldl_max_bound _ 0 _ (Nat.zero_le _)
  intro bits member
  obtain ⟨state,stateMember,bitMember⟩:=List.mem_flatMap.mp member
  exact safe state stateMember bits bitMember

end PDCompute.Pack
