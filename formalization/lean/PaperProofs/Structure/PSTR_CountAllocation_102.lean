module

public import PaperProofs.Structure.PSTR_ArbitrarySafe_101
public import PaperProofs.Structure.PSTR_CountCost_067

/-! Original fixed8192 allocation, full ROM/code footprint, and the real
terminal-fetch clause. These are numeric/safety lemmas, not FullClaims. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountAllocation

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open RawTreePreprocessingClaims

def allocation {q : Nat} (full : List (Finset (Fin q))) : Nat :=
  physicalHeaderWords + packedCapacityWords q
    (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) +
    8192 * (full.length + q + treeSize q full + 1)

theorem endpoint_le {q : Nat} (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    PSTRQueryLayout.endpoint
      (PSTRCountWorkspace.base q full (capacityWords 8192 full.length q (treeSize q full))
        (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ allocation full := by
  have he := PSTRQueryLayout.endpoint_index_factor full
    (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q) 8192 hq hl (by decide)
  rw [PSTRCountLogical.workspace_eq full _ _ hq] at he
  simpa only [treeSize, ne_of_gt hq, ite_false, allocation] using he

theorem input_size {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    (callInput q full command).size = full.length * q + 3 := by
  simp only [callInput, rawIncidenceROM, PhysicalROM.size, List.length_append,
    List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
  omega

theorem footprint_bound (raw packed product index base : Nat)
    (hraw : raw ≤ base ^ 2) (hpacked : packed ≤ product + 1)
    (hproduct : product ≤ 65538 * base ^ 4) (hindex : index ≤ 131072 * base ^ 3)
    (h2 : base ^ 2 ≤ base ^ 6)
    (hpowers : 1 ≤ base ^ 6 ∧ base ^ 3 ≤ base ^ 6 ∧ base ^ 4 ≤ base ^ 6) :
    raw + 3 + (4 + packed + index) + 2700 ≤ 16777216 * base ^ 6 := by
  omega

theorem footprint_fit {q : Nat} (full : List (Finset (Fin q))) (command : Command) :
    Fits (indexWidth 32 full.length q)
      ((callInput q full command).size + allocation full + (packingCode PSTRCountProgram.program).length) := by
  have hc := PA17A19QueryBridgeNumeric006b.capacity_bound full 8192 (by decide)
  have hw := PA17PackingBounds043.width_le_base full.length q
  have hm := Nat.mul_le_mul hc hw
  have hproduct : capacityWords 8192 full.length q (treeSize q full) * CapacityBits.width q ≤
      65538 * (full.length + q + 2) ^ 4 := by
    convert hm using 1
    ring
  have hp := PA17PackingBounds043.packedCapacityWords_le_product q
    (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q)
    (PA17PackingBounds043.bits_pos full.length q)
  have hi := PA17A19QueryBridgeNumeric006b.index_bound full 8192 (by decide)
  have hrom : full.length * q ≤ (full.length + q + 2) ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul
      (show full.length ≤ full.length + q + 2 by omega) (show q ≤ full.length + q + 2 by omega)
  have h2 : (full.length + q + 2) ^ 2 ≤ (full.length + q + 2) ^ 6 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have hs := PA17PackingBounds043.powers_le_six full.length q
  rw [input_size, PSTRCountProgram.code_length]
  apply PA17PackingBounds043.polynomial_fits
  unfold allocation physicalHeaderWords
  exact footprint_bound _ _ _ _ _ hrom hp hproduct hi h2 hs

theorem access_mono {bits : Nat} (rom : PhysicalROM) (small large : Nat)
    (state : WordState bits) (op : PackingOp) (hsize : small ≤ large)
    (ha : packingAccessFits rom small state op) : packingAccessFits rom large state op := by
  cases op with
  | arithmetic operation target left right => trivial
  | jumpIfZero condition target => trivial
  | base op =>
    cases op with
    | subtract target left right => trivial
    | base instruction =>
      cases instruction <;> simp only [packingAccessFits, AccessFits] at ha ⊢
      all_goals first | exact ha | exact ha.trans_le hsize

theorem atSafe_mono {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (small large : Nat) (state : WordState bits) (hsize : small ≤ large)
    (ha : PSTRCountKernel.AtSafe rom whole small state) :
    PSTRCountKernel.AtSafe rom whole large state := by
  obtain ⟨active, pc, op, decoded, access⟩ := ha
  exact ⟨active, pc, op, decoded, access_mono rom small large state op hsize access⟩

theorem terminal_access {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (heapWords : Nat) (state : WordState bits)
    (hwords : WordsFit bits (packingCode whole)) (hfit : Fits bits (5 * whole.length))
    (hp : state.pc = BitVec.ofNat bits (5 * whole.length)) (ha : state.halted = false) :
    state.halted = false ∧ state.pc.toNat + 4 < (packingCode whole).length ∧
      match PackingOp.decode (fetch whole state) with
      | none => fetch whole state = haltWords
      | some op => packingAccessFits rom heapWords state op := by
  have pc : state.pc.toNat = 5 * whole.length := by
    rw [hp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hfit
  have fetched : fetch whole state = natFetch whole (5 * whole.length) := by
    change physicalFetch bits (packingCode whole) _ = _
    rw [physicalFetch_eq bits _ _ hwords, pc]
    rfl
  refine ⟨ha, ?_, ?_⟩
  · rw [pc, packingCode_length]
    omega
  · rw [fetched, natFetch_halt, decode_halt]

end PaperProofs.Structure.LaminarTree.PSTRCountAllocation
