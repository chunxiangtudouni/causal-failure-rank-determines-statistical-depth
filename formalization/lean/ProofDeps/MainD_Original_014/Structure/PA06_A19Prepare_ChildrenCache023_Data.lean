module

public import Structure.PA06_A19Prepare_ChildrenCache023_Chunks
public import Structure.PA06_A19Prepare_CompactCandidates007
public import PaperProofs.Structure.RawCandidateSerializedChildrenRun

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled original-tree data interfaces for the actual children
cache. The ascending child/flat-list semantics and lengths are reused from
the already proved original ChildrenLayout/ChildrenPrefix serializer. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawCandidateChildrenLayout RawCandidateChildrenPrefix

abbrev preparedSize (q : Nat) (full : List (Finset (Fin q))) : Nat := (prepareNormalization q full).indexed.nodes.size
abbrev mass (q : Nat) (full : List (Finset (Fin q))) : Nat := full.length + q + 1

def parentWord (q : Nat) (full : List (Finset (Fin q))) (child : Nat) : Nat :=
  (givenTreeROM q full).internal.getD child 0

structure InputData (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState) : Prop where
  address : state.register .address = CB
  mass_cell : state.heap (CB + 528) = mass q full
  node_cell : state.heap (CB + 532 + 4 * mass q full) = preparedSize q full
  parents : ∀ child < preparedSize q full,
    state.heap (parentAddress CB (mass q full) child) = parentWord q full child

/-- This consumes the exact data equality delivered by the actual017 copy.
The scalar cache cells, prepared parents and node count all come from007. -/
theorem inputData_of_copiedCache {q : Nat} {full : List (Finset (Fin q))}
    {before after : NatState} (entry : PA06A19PrepareCompactCandidates007.ParentEntry q full before)
    (hq : 0 < q) (CB : Nat) (hCB : after.register .address = CB)
    (copied : ∀ address < PA06A19PrepareControlBank017.cacheLength full.length q,
      after.heap (CB + 512 + address) = before.heap address) : InputData q full CB after := by
  constructor
  · exact hCB
  · have h := copied 16 (by unfold PA06A19PrepareControlBank017.cacheLength; omega)
    have he : CB + 512 + 16 = CB + 528 := by omega
    rw [he, entry.count_cell] at h
    exact h
  · let source := RawCandidateParentRAM.nodeCountAddress 16 (mass q full)
    have hs : source < PA06A19PrepareControlBank017.cacheLength full.length q := by
      unfold source RawCandidateParentRAM.nodeCountAddress RawCandidateOrderingRAM.arraySlot
        PA06A19PrepareControlBank017.cacheLength PA06A19PrepareControlBank017.mass mass
      omega
    have h := copied source hs
    have he : CB + 512 + source = CB + 532 + 4 * mass q full := by
      unfold source RawCandidateParentRAM.nodeCountAddress RawCandidateOrderingRAM.arraySlot
      omega
    rw [he, entry.node_count hq] at h
    exact h
  · intro child hc
    have hchild : child < full.length + q + 1 := hc.trans_le (prepared_indexed_size_le q full)
    let source := RawCandidateParentRAM.parentSlot 16 (mass q full) child
    have hs : source < PA06A19PrepareControlBank017.cacheLength full.length q := by
      unfold source
      rw [RawCandidateParentRAM.parentSlot_eq]
      unfold PA06A19PrepareControlBank017.cacheLength PA06A19PrepareControlBank017.mass mass
      omega
    have h := copied source hs
    have he : CB + 512 + source = parentAddress CB (mass q full) child := by
      unfold source parentAddress
      rw [RawCandidateParentRAM.parentSlot_eq]
      omega
    rw [he, entry.parents ⟨child, hc⟩] at h
    exact h.trans (UniformNormalizationRAM.givenTreeROM_parent q full ⟨child, hc⟩).symm

/-- Only seven declared temporary control cells and the degree/child output
region may be changed. In particular the whole copied raw parent cache is
protected and .address preservation is a separate real-register fact. -/
def Protected (q : Nat) (full : List (Finset (Fin q))) (CB address : Nat) : Prop :=
  (address < CB + 64 ∨ CB + 71 ≤ address) ∧
    (address < degreeBase CB (mass q full) ∨
      childrenBase CB (mass q full) (preparedSize q full) + (preparedSize q full - 1) ≤ address)

def Frame (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (before after : NatState) : Prop :=
  ∀ address, Protected q full CB address → after.heap address = before.heap address

theorem Frame.refl (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState) :
    Frame q full CB state state := fun _ _ => rfl

theorem Frame.trans {q : Nat} {full : List (Finset (Fin q))} {CB : Nat} {a b c : NatState}
    (hab : Frame q full CB a b) (hbc : Frame q full CB b c) : Frame q full CB a c :=
  fun address h => (hbc address h).trans (hab address h)

theorem InputData.of_frame {q : Nat} {full : List (Finset (Fin q))} {CB : Nat} {before after : NatState}
    (input : InputData q full CB before) (frame : Frame q full CB before after)
    (address : after.register .address = before.register .address) : InputData q full CB after := by
  have hsize : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
  constructor
  · exact address.trans input.address
  · rw [frame _ (by unfold Protected degreeBase; constructor <;> omega)]
    exact input.mass_cell
  · rw [frame _ (by unfold Protected degreeBase; constructor <;> omega)]
    exact input.node_cell
  · intro child hc
    have hchild : child < mass q full := hc.trans_le hsize
    have hprotected : Protected q full CB (parentAddress CB (mass q full) child) := by
      constructor
      · apply Or.inr
        unfold parentAddress
        omega
      · apply Or.inl
        unfold parentAddress degreeBase
        omega
    rw [frame _ hprotected]
    exact input.parents child hc

/-- Exact original givenTreeROM data needed by constant-time getters.
This is an output specification; no proof of the whole producer is claimed
merely by defining it. -/
def OutputData (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) (state : NatState) : Prop :=
  InputData q full CB state ∧
  (∀ node : (prepareNormalization q full).indexed.NodeId,
    state.heap (degreeBase CB (mass q full) + node.val) =
      (givenTreeROM q full).internal.getD (preparedSize q full + node.val) 0) ∧
  (∀ position < (givenTreeROM q full).children.length,
    state.heap (childrenBase CB (mass q full) (preparedSize q full) + position) =
      (givenTreeROM q full).children.getD position 0)

/-- Pure child-list identity is reused verbatim; it is not presented as the
missing actual-machine producer theorem. -/
theorem exact_lists (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full) :
    (∀ node : (prepareNormalization q full).indexed.NodeId,
      (childIDs (preparedSize q full) (parentWord q full) node.val).length =
        (givenTreeROM q full).internal.getD (preparedSize q full + node.val) 0) ∧
    flatChildren (preparedSize q full) (parentWord q full) = (givenTreeROM q full).children ∧
    (flatChildren (preparedSize q full) (parentWord q full)).length = preparedSize q full - 1 := by
  refine ⟨?_, flatChildren_givenTreeROM q full, ?_⟩
  · intro node
    exact childIDs_length_eq_internalWord q full _ (givenTreeROM_parentWords q full) node
  · exact flatChildren_length q full _ (givenTreeROM_parentWords q full) hq hl

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
