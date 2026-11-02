module

public import Structure.PA06_A19Prepare_StaticMetadata036_ScanState

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Finite invariant update for a complete pair iteration, including its
real counter increment. Exact execution supplies pairHeap in ScanIteration;
no future-output theorem is a field in these loop states. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023 (preparedSize mass)

def pairHeap (q : Nat) (full : List (Finset (Fin q))) (reference : NatState) (CB P node tool : Nat)
    (heap : Nat → Nat) : Nat → Nat :=
  let stored := if scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node tool then
    Function.update (Function.update heap (fieldAddress P full.length (preparedSize q full) .leaf node) (tool + 1))
      (fieldAddress P full.length (preparedSize q full) .tool tool) (node + 1)
    else heap
  Function.update stored (CB + 20) (tool + 1)

private theorem pairHeap_apply (q : Nat) (full : List (Finset (Fin q)))
    (reference : NatState) (CB P node tool : Nat) (heap : Nat → Nat) (address : Nat) :
    pairHeap q full reference CB P node tool heap address =
      if address = CB + 20 then tool + 1 else
      if scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node tool then
        if address = fieldAddress P full.length (preparedSize q full) .tool tool then node + 1 else
        if address = fieldAddress P full.length (preparedSize q full) .leaf node then tool + 1 else heap address
      else heap address := by
  simp only [pairHeap, Function.update_apply, ite_apply]

theorem leaf_address_lt_tool (P N t node tool : Nat) (hn : node < t) :
    fieldAddress P N t .leaf node < fieldAddress P N t .tool tool := by
  simp only [fieldAddress, fieldFactor, fieldExtra]
  omega

theorem pairHeap_frame (q : Nat) (full : List (Finset (Fin q))) (reference : NatState) (CB P : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) (before after : NatState)
    (hh : after.heap = pairHeap q full reference CB P node.val tool.val before.heap) :
    ScanFrame q full CB P before after := by
  intro address hn
  have h20 : address ≠ CB + 20 := by unfold ScanAllowed at hn; omega
  have hleaf : address ≠ fieldAddress P full.length (preparedSize q full) .leaf node.val := by
    have hb : node.val < preparedSize q full := node.isLt
    simp only [ScanAllowed, fieldAddress, fieldFactor, fieldExtra] at *
    omega
  have htool : address ≠ fieldAddress P full.length (preparedSize q full) .tool tool.val := by
    have hb := tool.isLt
    simp only [ScanAllowed, fieldAddress, fieldFactor, fieldExtra] at *
    omega
  rw [hh]
  simp [pairHeap_apply, h20, hleaf, htool]

theorem pair_heap_ready (q : Nat) (full : List (Finset (Fin q))) (CB P : Nat)
    (reference : NatState) (referenceData : RawCardData q full CB reference)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) (pointer : Nat)
    (before after : NatState) (ready : LeafInnerReady q full CB P reference node tool.val pointer before)
    (hlayout : CB = 4 + P + 4096 * (mass q full + preparedSize q full))
    (hh : after.heap = pairHeap q full reference CB P node.val tool.val before.heap)
    (hCB : after.register .address = CB) (hpc : after.pc = pointer) (ha : after.halted = false) :
    LeafInnerReady q full CB P reference node (tool.val + 1) pointer after ∧
      ScanFrame q full CB P before after := by
  have frame := pairHeap_frame q full reference CB P node tool before after hh
  have below := scan_regions_below_control q full CB P hlayout
  have hn : node.val < preparedSize q full := node.isLt
  have ht := tool.isLt
  have hleaf : fieldAddress P full.length (preparedSize q full) .leaf node.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have htool : fieldAddress P full.length (preparedSize q full) .tool tool.val < CB := by
    simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
    omega
  have hcross := leaf_address_lt_tool P full.length (preparedSize q full) node.val tool.val hn
  have outside_control (address offset : Nat) (ha : address < CB) : address ≠ CB + offset := by
    omega
  have matchIndex := scanMatch_iff_index q full CB reference referenceData node tool
  refine ⟨?_, frame⟩
  constructor
  · exact ScanInput.of_frame ready.input hlayout frame hCB
  · rw [hh]
    simp [pairHeap_apply, (outside_control _ 19 hleaf).symm,
      (outside_control _ 19 htool).symm, ready.node_cell]
  · rw [hh]
    simp only [pairHeap, Function.update_self]
  · rw [hh]
    simp [pairHeap_apply, (outside_control _ 21 hleaf).symm,
      (outside_control _ 21 htool).symm, ready.card_cell]
  · rw [hh]
    simp [pairHeap_apply, outside_control _ 20 hleaf, ne_of_lt hcross,
      scanWinner, ready.row_leaf]
  · intro earlier he
    have he' : earlier.val < preparedSize q full := earlier.isLt
    have haddress : fieldAddress P full.length (preparedSize q full) .leaf earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    have hcross' := leaf_address_lt_tool P full.length (preparedSize q full) earlier.val tool.val he'
    have hne : fieldAddress P full.length (preparedSize q full) .leaf earlier.val ≠
        fieldAddress P full.length (preparedSize q full) .leaf node.val := by
      simp only [fieldAddress]
      omega
    rw [hh]
    simpa [pairHeap_apply, outside_control _ 20 haddress, ne_of_lt hcross', hne]
      using ready.leaves earlier he
  · intro earlier he
    have he' := earlier.isLt
    have haddress : fieldAddress P full.length (preparedSize q full) .tool earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    have hcross' := leaf_address_lt_tool P full.length (preparedSize q full) node.val earlier.val hn
    rw [hh]
    by_cases hm : scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node.val tool.val = true
    · have hindex := matchIndex.mp hm
      have hne : earlier.val ≠ tool.val := by
        intro heq
        have hetool : earlier = tool := Fin.ext heq
        rw [hetool, hindex] at he
        omega
      have haddress_ne : fieldAddress P full.length (preparedSize q full) .tool earlier.val ≠
          fieldAddress P full.length (preparedSize q full) .tool tool.val := by
        simp only [fieldAddress]
        omega
      simpa [pairHeap_apply, outside_control _ 20 haddress, (ne_of_lt hcross').symm,
        hm, haddress_ne]
        using ready.tools earlier he
    · have hf : scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node.val tool.val = false := by
        cases hh : scanMatch (rawIncidenceROM q full) reference.heap CB (mass q full) node.val tool.val <;> simp_all
      simpa [pairHeap_apply, outside_control _ 20 haddress, hf] using ready.tools earlier he
  · intro earlier he hindex
    have he' := earlier.isLt
    have haddress : fieldAddress P full.length (preparedSize q full) .tool earlier.val < CB := by
      simp only [fieldAddress, fieldFactor, fieldExtra] at below ⊢
      omega
    have hcross' := leaf_address_lt_tool P full.length (preparedSize q full) node.val earlier.val hn
    rw [hh]
    by_cases heq : earlier.val = tool.val
    · have hetool : earlier = tool := Fin.ext heq
      subst earlier
      have hm := matchIndex.mpr hindex
      simp [pairHeap_apply, outside_control _ 20 haddress, hm]
    · have hbefore : earlier.val < tool.val := by omega
      have haddress_ne : fieldAddress P full.length (preparedSize q full) .tool earlier.val ≠
          fieldAddress P full.length (preparedSize q full) .tool tool.val := by
        simp only [fieldAddress]
        omega
      simpa [pairHeap_apply, outside_control _ 20 haddress, (ne_of_lt hcross').symm, haddress_ne]
        using ready.row_tools earlier hbefore hindex
  · exact hpc
  · exact ha

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
