module

public import PaperProofs.Structure.PSTR_HD_HeadsZeroAdvanceRun_092

/-! Every scratch/output prefix preserves ORIGINAL q0 Rep. Only the real
six low cells matter; the shared controller writes actual cells>=46. No
positive cache/tree or input field is used in this q0 representation proof. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem zero_init_prefix_rep {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (he : Fits bits (46 + 8)) (haddr : state.register .address = BitVec.ofNat bits 46)
    (count : Nat) (hc : count ≤ headsInit.length) :
    HeapRepresents 0 full 0 configuration
      (executeOps (callInput 0 full .query) (headsInit.take count) state).heap := by
  apply zero_rep_frame full configuration state.heap _ rep
  intro physical hp
  exact headsInit_prefix_frame (callInput 0 full .query) 46 state hb haddr he physical
    ((show physical ≤ 46 + 8 by omega).trans_lt he) (Or.inl (by omega)) count hc

theorem zero_append_prefix_rep {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (rank : Nat) (entries : List Nat) (state : WordState bits)
    (rep : HeapRepresents 0 full 0 configuration state.heap)
    (recorded : RecordedHeads 46 0 rank entries state.heap)
    (he : Fits bits (46 + 10 + entries.length + 1)) (haddr : state.register .address = BitVec.ofNat bits 46)
    (count : Nat) (hc : count ≤ headsAppend.length) :
    HeapRepresents 0 full 0 configuration
      (executeOps (callInput 0 full .query) (headsAppend.take count) state).heap := by
  apply zero_rep_frame full configuration state.heap _ rep
  intro physical hp
  exact headsAppend_prefix_frame (callInput 0 full .query) 46 (46 + 10 + entries.length) state haddr recorded.cursor
    ((show 46 + 2 ≤ 46 + 10 + entries.length + 1 by omega).trans_lt he)
    ((Nat.le_add_right _ 1).trans_lt he) physical ((show physical ≤ 46 + 10 + entries.length + 1 by omega).trans_lt he)
    (by omega) (by omega) (by omega) count hc

theorem zero_finish_prefix_rep {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (state : WordState bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (he : Fits bits (46 + 9)) (haddr : state.register .address = BitVec.ofNat bits 46)
    (count : Nat) (hc : count ≤ headsFinish.length) :
    HeapRepresents 0 full 0 configuration
      (executeOps (callInput 0 full .query) (headsFinish.take count) state).heap := by
  apply zero_rep_frame full configuration state.heap _ rep
  intro physical hp
  exact headsFinish_prefix_frame (callInput 0 full .query) 46 state haddr he physical
    ((show physical ≤ 46 + 9 by omega).trans_lt he) (by omega) count hc

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
