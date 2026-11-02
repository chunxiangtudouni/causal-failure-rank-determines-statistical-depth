module

public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.PA17_CellLayout_003
public import PaperProofs.Structure.PA17_PackedStore_042b
public import PaperProofs.Structure.PA17_PackedTranslator_034b
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/-! Private uncompiled A19/A17 double-cutoff physical views.
These are representation/update/frame lemmas, not an ISA implementation.
The capacity cutoff is the ORIGINAL A19 C; old A17 ordinary words start at
an explicit physical indexBase after the actual packed region. In particular
old metadata is never silently reclassified as an A19 capacity scalar. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePackedView013

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open CompactControllerClaims (dataHeap logicalHeap)
open AlgorithmClaims.PackedCapacityRAM

variable {bits : Nat}

def oldCapacity (N q t : Nat) : Nat := tableWords N q t + 2 * (t + 1)
def capacity (N q t : Nat) : Nat := CompactControllerClaims.capacityWords 8192 N q t

theorem oldCapacity_eq_A17 (N q t : Nat) :
    oldCapacity N q t = PA17CellLayout003.capacityWords N q t := rfl

theorem oldCapacity_le_capacity (N q t : Nat) (hq : 0 < q) :
    oldCapacity N q t ≤ capacity N q t := by
  unfold oldCapacity capacity CompactControllerClaims.capacityWords
  rw [ite_eq_right (Nat.ne_of_gt hq)]
  omega

theorem tableWords_le_oldCapacity (N q t : Nat) :
    tableWords N q t ≤ oldCapacity N q t := Nat.le_add_right _ _

/-- Old logical A17 heap viewed in the SAME actual physical Word heap.
Only old a<C0 reads the actual A19 packed prefix; a>=C0 always goes to the
ordinary physical bank indexBase+(a-C0), with no packed decoder there. -/
def view (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits) (a : Nat) : Nat :=
  if a < C0 then unpackHeap q C bits (dataHeap heap) a
  else (heap (BitVec.ofNat bits (indexBase + (a - C0)))).toNat

theorem view_capacity (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits)
    (a : Nat) (ha : a < C0) :
    view q C0 C indexBase heap a = unpackHeap q C bits (dataHeap heap) a := by
  simp only [view, ha, ite_true]

theorem view_index (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits)
    (a : Nat) (ha : C0 ≤ a) :
    view q C0 C indexBase heap a = (heap (BitVec.ofNat bits (indexBase + (a - C0)))).toNat := by
  simp only [view, not_lt_of_ge ha, ite_false]

theorem view_capacity_scalar (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits)
    (hC : C0 ≤ C) (a : Nat) (ha : a < C0) :
    view q C0 C indexBase heap a =
      CapacityBits.decodeScalar (List.ofFn (fun position : Fin (CapacityBits.width q) =>
        let offset := a * CapacityBits.width q + position.val
        ((dataHeap heap) (BitVec.ofNat bits (offset / bits))).getLsbD (offset % bits))) := by
  rw [view_capacity q C0 C indexBase heap a ha, unpackHeap, ite_eq_left (ha.trans_le hC)]

/-- Genuine modular +4 identity, not a no-wrap assumption. -/
theorem dataHeap_word (heap : BitVec bits → BitVec bits) (a : Nat) :
    dataHeap heap (BitVec.ofNat bits a) = heap (BitVec.ofNat bits (4 + a)) := by
  unfold dataHeap CompactControllerClaims.physicalHeaderWords
  apply congrArg heap
  rw [← BitVec.ofNat_add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.ofNat_add_ofNat]

theorem dataHeap_update (heap : BitVec bits → BitVec bits) (a : Nat) (value : BitVec bits) :
    dataHeap (Function.update heap (BitVec.ofNat bits (4 + a)) value) =
      Function.update (dataHeap heap) (BitVec.ofNat bits a) value := by
  funext word
  have heq : BitVec.ofNat bits (4 + word.toNat) = BitVec.ofNat bits (4 + a) ↔
      word = BitVec.ofNat bits a := by
    rw [← BitVec.ofNat_add_ofNat, ← BitVec.ofNat_add_ofNat,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_right_inj (BitVec.ofNat bits 4)
  simp only [dataHeap, CompactControllerClaims.physicalHeaderWords, Function.update_apply, heq]

theorem view_index_dataHeap (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 4 ≤ indexBase) (a : Nat) (ha : C0 ≤ a) :
    view q C0 C indexBase heap a =
      ((dataHeap heap) (BitVec.ofNat bits (indexBase - 4 + (a - C0)))).toNat := by
  have haddr : 4 + (indexBase - 4 + (a - C0)) = indexBase + (a - C0) := by omega
  rw [view_index q C0 C indexBase heap a ha, dataHeap_word, haddr]

/-- Explicit embedding of each old ordinary word into the ORIGINAL A19
ordinary logical suffix. Address Fits/access remain separate obligations. -/
theorem view_index_logicalHeap (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) (hb : 4 + packedCapacityWords q C bits ≤ indexBase)
    (a : Nat) (ha : C0 ≤ a) :
    view q C0 C indexBase heap a = logicalHeap q C heap
      (C + (indexBase - (4 + packedCapacityWords q C bits)) + (a - C0)) := by
  rw [view_index q C0 C indexBase heap a ha]
  unfold logicalHeap
  rw [ite_eq_right (Nat.ne_of_gt hq), unpackHeap, ite_eq_right (by omega)]
  rw [dataHeap_word]
  have haddr : 4 + (packedCapacityWords q C bits +
      (C + (indexBase - (4 + packedCapacityWords q C bits)) + (a - C0) - C)) =
      indexBase + (a - C0) := by omega
  rw [haddr]

/-- Capacity representation transport only: it does not assert an execution. -/
theorem capacityPrefixBounded_of_new (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits)
    (hC : C0 ≤ C) (hbound : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap heap))) :
    CapacityPrefixBounded q C0 (view q C0 C indexBase heap) := by
  intro a ha
  rw [view_capacity q C0 C indexBase heap a ha]
  exact hbound a (ha.trans_le hC)

/-- The extra A19 capacity cells are explicit; old C0-boundedness alone is
not misreported as boundedness of the much larger original A19 C. -/
theorem capacityPrefixBounded_iff (q C0 C indexBase : Nat) (heap : BitVec bits → BitVec bits)
    (hC : C0 ≤ C) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap heap)) ↔
      CapacityPrefixBounded q C0 (view q C0 C indexBase heap) ∧
        (∀ a, C0 ≤ a → a < C → unpackHeap q C bits (dataHeap heap) a ≤ q) := by
  constructor
  · intro h
    exact ⟨capacityPrefixBounded_of_new q C0 C indexBase heap hC h, fun a _ ha => h a ha⟩
  · rintro ⟨hold, htail⟩ a ha
    by_cases hsmall : a < C0
    · have hh := hold a hsmall
      rwa [view_capacity q C0 C indexBase heap a hsmall] at hh
    · exact htail a (by omega) ha

/-- Pointwise prefix transport can be applied to a genuinely proved trace.
No trace/safety/correctness conclusion is assumed about a preprocessor. -/
theorem prefix_capacity_transport (q C0 C indexBase : Nat)
    (heaps : Nat → BitVec bits → BitVec bits) (steps : Nat) (hC : C0 ≤ C)
    (hbound : ∀ clock ≤ steps,
      CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap (heaps clock)))) :
    ∀ clock ≤ steps, CapacityPrefixBounded q C0 (view q C0 C indexBase (heaps clock)) := by
  intro clock hc
  exact capacityPrefixBounded_of_new q C0 C indexBase _ hC (hbound clock hc)

private theorem readEntry_congr_prefix (t slot limit : Nat) (left right : Nat → Nat)
    (hslot : (slot + 1) * (t + 1) ≤ limit)
    (heq : ∀ a < limit, left a = right a) :
    readEntry t slot left = readEntry t slot right := by
  have htag : left (slot * (t + 1)) = right (slot * (t + 1)) :=
    heq _ (by nlinarith)
  unfold readEntry
  rw [htag]
  split_ifs
  · rfl
  · apply congrArg CapacityBits.Entry.vector
    apply congrArg Vector.ofFn
    funext node
    apply heq
    have hn := node.isLt
    nlinarith

private theorem slot_end_le (N q t : Nat) (stage : Fin (N + 1)) (budget : Fin (q + 2)) :
    (stage.val * (q + 2) + budget.val + 1) * (t + 1) ≤ tableWords N q t := by
  have hslot : stage.val * (q + 2) + budget.val + 1 ≤ (N + 1) * (q + 2) := by
    calc
      stage.val * (q + 2) + budget.val + 1 ≤ (stage.val + 1) * (q + 2) := by
        rw [Nat.add_mul, Nat.one_mul]
        have hb := budget.isLt
        omega
      _ ≤ (N + 1) * (q + 2) :=
        Nat.mul_le_mul_right (q + 2) (Nat.succ_le_of_lt stage.isLt)
  exact Nat.mul_le_mul_right (t + 1) hslot

theorem physicalTableCorrect_congr_prefix (q : Nat) (full : List (Finset (Fin q)))
    (left right : Nat → Nat)
    (heq : ∀ a < tableWords full.length q (prepareNormalization q full).indexed.nodes.size,
      left a = right a) : PhysicalTableCorrect q full left ↔ PhysicalTableCorrect q full right := by
  let t := (prepareNormalization q full).indexed.nodes.size
  have transport (first second : Nat → Nat)
      (he : ∀ a < tableWords full.length q t, first a = second a)
      (hc : PhysicalTableCorrect q full first) : PhysicalTableCorrect q full second := by
    constructor
    · intro stage budget
      rw [← readEntry_congr_prefix t _ (tableWords full.length q t) first second
        (slot_end_le full.length q t stage budget) he]
      exact hc.1 stage budget
    · intro slot hs
      have hp : slot * (t + 1) < tableWords full.length q t := by
        simpa only [tableWords] using Nat.mul_lt_mul_of_pos_right hs (Nat.succ_pos t)
      rw [← he _ hp]
      exact hc.2 slot hs
  exact ⟨transport left right heq, transport right left (fun a ha => (heq a ha).symm)⟩

theorem physicalTableCorrect_view_iff (q : Nat) (full : List (Finset (Fin q)))
    (C indexBase : Nat) (heap : BitVec bits → BitVec bits) :
    PhysicalTableCorrect q full
        (view q (oldCapacity full.length q (prepareNormalization q full).indexed.nodes.size) C indexBase heap) ↔
      PhysicalTableCorrect q full (unpackHeap q C bits (dataHeap heap)) := by
  apply physicalTableCorrect_congr_prefix
  intro a ha
  exact view_capacity _ _ _ _ _ a (ha.trans_le (tableWords_le_oldCapacity _ _ _))

/-- Mathematical physical update matching PackedCapacityRAM.writeHeap with
the ORIGINAL physical +4 header displacement. It is not new write ISA. -/
def packedStore (q a : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  Function.update
    (Function.update heap (BitVec.ofNat bits (4 + a * CapacityBits.width q / bits))
      (writeLow (CapacityBits.width q) (a * CapacityBits.width q % bits) value
        (heap (BitVec.ofNat bits (4 + a * CapacityBits.width q / bits)))))
    (BitVec.ofNat bits (4 + (a * CapacityBits.width q / bits + 1)))
    (writeHigh (CapacityBits.width q) (a * CapacityBits.width q % bits) value
      (heap (BitVec.ofNat bits (4 + (a * CapacityBits.width q / bits + 1)))))

theorem dataHeap_packedStore (q a : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    dataHeap (packedStore q a value heap) =
      writeHeap (CapacityBits.width q) (a * CapacityBits.width q) value (dataHeap heap) := by
  simp only [packedStore, dataHeap_update, writeHeap, dataHeap_word]

/-- One physical capacity-field replacement is the corresponding old heap
update throughout its allocated old address domain. No metadata is packed. -/
theorem view_packedStore (q C0 C indexBase indexWords a : Nat)
    (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits) (hC : C0 ≤ C)
    (ha : a < C0) (hnext : Fits bits (a * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (C * CapacityBits.width q))
    (hvalue : value.toNat ≤ q)
    (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hend : Fits bits (indexBase + indexWords))
    (other : Nat) (ho : other < C0 + indexWords) :
    view q C0 C indexBase (packedStore q a value heap) other =
      (Function.update (view q C0 C indexBase heap) a value.toNat) other := by
  have hv := CapacityBits.value_lt_two_pow_width q value.toNat hvalue
  by_cases he : other = a
  · subst other
    rw [Function.update_self, view_capacity q C0 C indexBase _ a ha, dataHeap_packedStore]
    exact unpackHeap_write_target q C a value (dataHeap heap) hbits hwidth (ha.trans_le hC) hnext hv
  · rw [Function.update_of_ne he]
    by_cases hoc : other < C0
    · rw [view_capacity q C0 C indexBase _ other hoc,
        view_capacity q C0 C indexBase heap other hoc, dataHeap_packedStore]
      exact unpackHeap_write_other_capacity q C a other value (dataHeap heap)
        hbits hwidth hnext hregion hv (hoc.trans_le hC) he
    · have hother : C0 ≤ other := by omega
      have hoffset : Fits bits (indexBase - 4 + (other - C0)) :=
        lt_of_le_of_lt (by omega) hend
      rw [view_index_dataHeap q C0 C indexBase _ (by omega) other hother,
        view_index_dataHeap q C0 C indexBase heap (by omega) other hother, dataHeap_packedStore,
        PA17PackedStore042b.writeHeap_physical_frame q C a (indexBase - 4 + (other - C0))
          value (dataHeap heap) hbits hwidth (ha.trans_le hC) (by omega) hoffset hnext hv]

/-- The larger A19 capacity bound is preserved, including its explicit
extra cells, when an old capacity field is replaced by a value<=q. -/
theorem packedStore_capacityBounded (q C a : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits)
    (hwidth : CapacityBits.width q ≤ bits) (ha : a < C)
    (hnext : Fits bits (a * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (C * CapacityBits.width q)) (hv : value.toNat ≤ q)
    (hbound : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap heap))) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap (packedStore q a value heap))) := by
  intro other ho
  rw [dataHeap_packedStore]
  by_cases he : other = a
  · subst other
    rw [unpackHeap_write_target q C a value (dataHeap heap) hbits hwidth ha hnext
      (CapacityBits.value_lt_two_pow_width q _ hv)]
    exact hv
  · rw [unpackHeap_write_other_capacity q C a other value (dataHeap heap) hbits hwidth hnext
      hregion (CapacityBits.value_lt_two_pow_width q _ hv) ho he]
    exact hbound other ho

/-- Ordinary old logical storage is a single actual physical Word update. -/
def indexStore (C0 indexBase a : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits := Function.update heap (BitVec.ofNat bits (indexBase + (a - C0))) value

theorem indexStore_capacity_frame (q C0 C indexBase a : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits)
    (hregion : Fits bits (C * CapacityBits.width q))
    (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hphysical : Fits bits (indexBase + (a - C0)))
    (other : Nat) (ho : other < C) :
    unpackHeap q C bits (dataHeap (indexStore C0 indexBase a value heap)) other =
      unpackHeap q C bits (dataHeap heap) other := by
  have hp : indexBase + (a - C0) = 4 + (indexBase - 4 + (a - C0)) := by omega
  rw [indexStore, hp, dataHeap_update]
  exact PA17PackedTranslator034.index_update_capacity q C _ value (dataHeap heap) hbits hregion
    (by omega) (lt_of_le_of_lt (by omega) hphysical) other ho

theorem view_indexStore (q C0 C indexBase indexWords a : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits) (hC : C0 ≤ C)
    (hregion : Fits bits (C * CapacityBits.width q))
    (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (ha : C0 ≤ a) (had : a < C0 + indexWords) (hend : Fits bits (indexBase + indexWords))
    (other : Nat) (ho : other < C0 + indexWords) :
    view q C0 C indexBase (indexStore C0 indexBase a value heap) other =
      (Function.update (view q C0 C indexBase heap) a value.toNat) other := by
  have hp : Fits bits (indexBase + (a - C0)) := lt_of_lt_of_le (by omega) hend.le
  by_cases he : other = a
  · subst other
    rw [Function.update_self, view_index q C0 C indexBase _ a ha]
    simp only [indexStore, Function.update_self]
  · rw [Function.update_of_ne he]
    by_cases hoc : other < C0
    · rw [view_capacity q C0 C indexBase _ other hoc, view_capacity q C0 C indexBase heap other hoc]
      exact indexStore_capacity_frame q C0 C indexBase a value heap hbits hregion hbase hp other (hoc.trans_le hC)
    · have hot : C0 ≤ other := by omega
      have hop : Fits bits (indexBase + (other - C0)) := lt_of_lt_of_le (by omega) hend.le
      have hne : BitVec.ofNat bits (indexBase + (other - C0)) ≠
          BitVec.ofNat bits (indexBase + (a - C0)) :=
        (ofNat_injective_of_fit _ _ hop hp).not.mpr (by omega)
      rw [view_index q C0 C indexBase _ other hot, view_index q C0 C indexBase heap other hot,
        indexStore, Function.update_of_ne hne]

theorem indexStore_capacityBounded (q C0 C indexBase a : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits)
    (hregion : Fits bits (C * CapacityBits.width q))
    (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hphysical : Fits bits (indexBase + (a - C0)))
    (hbound : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap heap))) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap (indexStore C0 indexBase a value heap))) := by
  intro other ho
  rw [indexStore_capacity_frame q C0 C indexBase a value heap hbits hregion hbase hphysical other ho]
  exact hbound other ho

/-- Actual +4 update leaves all four physical headers untouched once the
absolute second-word pointer Fits; decoder-relative Fits alone is not used
as a substitute for this physical address condition. -/
theorem packedStore_header_frame (q a header : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hh : header < 4)
    (hphysical : Fits bits (4 + (a * CapacityBits.width q / bits + 1))) :
    packedStore q a value heap (BitVec.ofNat bits header) =
      heap (BitVec.ofNat bits header) := by
  have hheader_low : header < 4 + a * CapacityBits.width q / bits :=
    hh.trans_le (Nat.le_add_right 4 (a * CapacityBits.width q / bits))
  have hheader_high : header < 4 + (a * CapacityBits.width q / bits + 1) :=
    hh.trans_le (Nat.le_add_right 4 (a * CapacityBits.width q / bits + 1))
  have hhfit : Fits bits header := hheader_high.trans hphysical
  have hlofit : Fits bits (4 + a * CapacityBits.width q / bits) :=
    (Nat.add_le_add_left (Nat.le_succ (a * CapacityBits.width q / bits)) 4).trans_lt hphysical
  have hnhi : BitVec.ofNat bits header ≠
      BitVec.ofNat bits (4 + (a * CapacityBits.width q / bits + 1)) :=
    (ofNat_injective_of_fit _ _ hhfit hphysical).not.mpr (Nat.ne_of_lt hheader_high)
  have hnlo : BitVec.ofNat bits header ≠
      BitVec.ofNat bits (4 + a * CapacityBits.width q / bits) :=
    (ofNat_injective_of_fit _ _ hhfit hlofit).not.mpr (Nat.ne_of_lt hheader_low)
  simp only [packedStore, Function.update_of_ne hnhi, Function.update_of_ne hnlo]

theorem indexStore_header_frame (C0 indexBase a header : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbase : 4 ≤ indexBase) (hh : header < 4)
    (hphysical : Fits bits (indexBase + (a - C0))) :
    indexStore C0 indexBase a value heap (BitVec.ofNat bits header) =
      heap (BitVec.ofNat bits header) := by
  have hhfit : Fits bits header := lt_of_le_of_lt (by omega) hphysical
  have hn : BitVec.ofNat bits header ≠ BitVec.ofNat bits (indexBase + (a - C0)) :=
    (ofNat_injective_of_fit _ _ hhfit hphysical).not.mpr (by omega)
  exact Function.update_of_ne hn value heap

/-- Ordinary-bank writes preserve the genuine A19 table predicate. -/
theorem physicalTableCorrect_indexStore (q : Nat) (full : List (Finset (Fin q)))
    (C0 C indexBase a : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hbits : 0 < bits) (hregion : Fits bits (C * CapacityBits.width q))
    (hbase : 4 + packedCapacityWords q C bits ≤ indexBase)
    (hphysical : Fits bits (indexBase + (a - C0)))
    (htable : tableWords full.length q (prepareNormalization q full).indexed.nodes.size ≤ C)
    (hc : PhysicalTableCorrect q full (unpackHeap q C bits (dataHeap heap))) :
    PhysicalTableCorrect q full (unpackHeap q C bits (dataHeap (indexStore C0 indexBase a value heap))) := by
  apply (physicalTableCorrect_congr_prefix q full _ _ (fun other ho =>
    (indexStore_capacity_frame q C0 C indexBase a value heap hbits hregion hbase hphysical
      other (ho.trans_le htable)).symm)).mp
  exact hc

/-- A workspace capacity write outside tableWords preserves the genuine
table predicate, using the existing packed writer's scalar frame. -/
theorem physicalTableCorrect_packedStore (q : Nat) (full : List (Finset (Fin q)))
    (C a : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits) (ha : a < C)
    (hnext : Fits bits (a * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (C * CapacityBits.width q)) (hv : value.toNat ≤ q)
    (hafter : tableWords full.length q (prepareNormalization q full).indexed.nodes.size ≤ a)
    (hc : PhysicalTableCorrect q full (unpackHeap q C bits (dataHeap heap))) :
    PhysicalTableCorrect q full (unpackHeap q C bits (dataHeap (packedStore q a value heap))) := by
  have heq : ∀ other < tableWords full.length q (prepareNormalization q full).indexed.nodes.size,
      unpackHeap q C bits (dataHeap heap) other =
        unpackHeap q C bits (dataHeap (packedStore q a value heap)) other := by
    intro other ho
    rw [dataHeap_packedStore]
    exact (unpackHeap_write_other_capacity q C a other value (dataHeap heap) hbits hwidth
      hnext hregion (CapacityBits.value_lt_two_pow_width q _ hv)
      (lt_of_lt_of_le ho (hafter.trans ha.le)) (by omega)).symm
  exact (physicalTableCorrect_congr_prefix q full _ _ heq).mp hc

end PaperProofs.Structure.LaminarTree.PA06A19PreparePackedView013
