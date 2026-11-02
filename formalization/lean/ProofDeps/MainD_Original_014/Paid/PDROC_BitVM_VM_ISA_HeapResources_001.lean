module

public import Paid.PDROC_BitVM_VM_ISA_Specification_003
public import Paid.PDROC_BitVM_Log_HeapLoad_042
public import Paid.PDROC_BitVM_Log_HeapStore_031
public import Paid.PDROC_BitVM_Log_HeapRelease_024

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.HeapResources

open PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

/-! Pure charges for the actual old opcode budgets. The size below is
exactly Spec003's entry tape size. It is not a new workspace input or a
P-only bound on scratch. In particular record count is proved from bytes. -/

def base (input : List Cell) (contents : Stack → List Bool) :=
  Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1

theorem base_positive (input : List Cell) (contents : Stack → List Bool) : 1 ≤ base input contents := by
  unfold base
  omega

theorem data_le_base (input : List Cell) (contents : Stack → List Bool) :
    Kernel.NatInstruction.dataSize contents ≤ base input contents := by unfold base; omega

theorem input_le_base (input : List Cell) (contents : Stack → List Bool) :
    (encodeBits input).length ≤ base input contents := by unfold base; omega

theorem base_le_square (input : List Cell) (contents : Stack → List Bool) :
    base input contents ≤ (base input contents)^2 := by
  simpa only [pow_two, Nat.mul_one] using
    Nat.mul_le_mul_left (base input contents) (base_positive input contents)

theorem record_positive (event : Log.HeapEvent) : 1 ≤ (Log.encodeEvent event).length := by
  cases tag : event.value <;> simp [Log.encodeEvent, tag]

theorem events_le_history (events : List Log.HeapEvent) : events.length ≤ (Log.encodeHistory events).length := by
  induction events using List.reverseRecOn with
  | nil => simp [Log.encodeHistory]
  | append_singleton previous event ih =>
    have positive := record_positive event
    rw [Log.encodeHistory_append]
    simp only [List.length_append, List.length_singleton]
    omega

theorem lookup_cell_le_history (events : List Log.HeapEvent) (query : ℕ) (value : Cell)
    (found : Log.lookup events query = some value) :
    (encodeCellBits value).length ≤ (Log.encodeHistory events).length := by
  revert query value
  induction events using List.reverseRecOn with
  | nil => intro query value found; simp only [Log.lookup_nil, reduceCtorEq] at found
  | append_singleton previous event ih =>
    intro query value found
    rw [Log.lookup_append] at found
    by_cases same : query = event.address
    · subst query
      rw [Function.update_self] at found
      have payload : (encodeCellBits value).length ≤ (Log.encodeEvent event).length := by
        simp only [Log.encodeEvent, found, List.length_cons, List.length_append]
        omega
      rw [Log.encodeHistory_append, List.length_append]
      omega
    · rw [Function.update_of_ne same] at found
      have previousBound := ih query value found
      rw [Log.encodeHistory_append, List.length_append]
      omega

theorem register_word (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (ready : Source.Ready input logical events contents) (reg : Register) :
    (encodeCellBits (logical.register reg)).length ≤ Kernel.NatInstruction.dataSize contents := by
  have bound := Kernel.NatInstruction.dataSize_each contents (registerSlot reg)
  rw [ready.registers reg] at bound
  exact bound

theorem pointer_word (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (ready : Source.Ready input logical events contents) (pointer : Register) (query : ℕ)
    (natural : logical.register pointer = .natural query) :
    (encodeNatBits query).length ≤ Kernel.NatInstruction.dataSize contents := by
  have bound := register_word input logical events contents ready pointer
  rw [natural] at bound
  simp only [encodeCellBits, List.length_cons] at bound
  omega

theorem workCap_bound (contents : Stack → List Bool) :
    Log.HeapLoad.workCap contents ≤ 6 * Kernel.NatInstruction.dataSize contents := by
  have w24 := Kernel.NatInstruction.dataSize_each contents 24
  have w25 := Kernel.NatInstruction.dataSize_each contents 25
  have w26 := Kernel.NatInstruction.dataSize_each contents 26
  have w27 := Kernel.NatInstruction.dataSize_each contents 27
  have w28 := Kernel.NatInstruction.dataSize_each contents 28
  have w29 := Kernel.NatInstruction.dataSize_each contents 29
  unfold Log.HeapLoad.workCap
  omega

theorem inputLoad_budget (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (ready : Source.Ready input logical events contents) (pointer destination : Register) :
    Log.InputLoad.opcodeBudget input logical pointer destination contents ≤ 4096 * (base input contents)^2 := by
  have work := workCap_bound contents
  have ptr := register_word input logical events contents ready pointer
  have dst := register_word input logical events contents ready destination
  have data := data_le_base input contents
  have bytes := input_le_base input contents
  have positive := base_positive input contents
  have square := base_le_square input contents
  change 6 * (Log.HeapLoad.workCap contents + 3) +
    3 * (encodeCellBits (logical.register pointer)).length +
    (encodeCellBits (logical.register destination)).length + 2 * (encodeBits input).length + 1000 ≤ _
  nlinarith

theorem load_budget (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (ready : Source.Ready input logical events contents) (pointer destination : Register)
    (query : ℕ) (value : Cell) (natural : logical.register pointer = .natural query)
    (found : Log.lookup events query = some value) :
    Log.HeapLoad.foundBudget events query destination value contents ≤ 4096 * (base input contents)^2 := by
  have work := workCap_bound contents
  have ptr := pointer_word input logical events contents ready pointer query natural
  have dst := Kernel.NatInstruction.dataSize_each contents (registerSlot destination)
  have history : (Log.encodeHistory events).length ≤ Kernel.NatInstruction.dataSize contents := by
    rw [← ready.history]
    exact Kernel.NatInstruction.dataSize_each contents 21
  have records := events_le_history events
  have payload := lookup_cell_le_history events query value found
  have historyBase : (Log.encodeHistory events).length + 1 ≤ base input contents := by unfold base; omega
  have recordsBase : events.length + 1 ≤ base input contents := by omega
  have product : (events.length + 1) * ((Log.encodeHistory events).length + 1) ≤ (base input contents)^2 := by
    simpa only [pow_two] using Nat.mul_le_mul recordsBase historyBase
  have scaled : 100 * (events.length + 1) * ((Log.encodeHistory events).length + 1) ≤
      100 * (base input contents)^2 := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 100 product
  have data := data_le_base input contents
  have positive := base_positive input contents
  have square := base_le_square input contents
  unfold Log.HeapLoad.foundBudget Log.HeapLoad.queryBudget Log.HeapLoad.clearBudget
  nlinarith

theorem store_budget (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (ready : Source.Ready input logical events contents) (pointer source : Register) (address : ℕ)
    (natural : logical.register pointer = .natural address) :
    Log.HeapStore.clearBudget contents + (contents 28).length +
      50 * ((encodeNatBits address).length + (encodeCellBits (logical.register source)).length + 1) ≤
      4096 * (base input contents)^2 := by
  have w24 := Kernel.NatInstruction.dataSize_each contents 24
  have w25 := Kernel.NatInstruction.dataSize_each contents 25
  have w26 := Kernel.NatInstruction.dataSize_each contents 26
  have w28 := Kernel.NatInstruction.dataSize_each contents 28
  have ptr := pointer_word input logical events contents ready pointer address natural
  have src := register_word input logical events contents ready source
  have data := data_le_base input contents
  have positive := base_positive input contents
  have square := base_le_square input contents
  unfold Log.HeapStore.clearBudget
  nlinarith

theorem release_budget (input : List Cell) (logical : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (ready : Source.Ready input logical events contents) (pointer : Register) (address : ℕ)
    (natural : logical.register pointer = .natural address) :
    Log.HeapRelease.clearBudget contents + 30 * ((encodeNatBits address).length + 1) ≤
      4096 * (base input contents)^2 := by
  have w24 := Kernel.NatInstruction.dataSize_each contents 24
  have w25 := Kernel.NatInstruction.dataSize_each contents 25
  have w26 := Kernel.NatInstruction.dataSize_each contents 26
  have ptr := pointer_word input logical events contents ready pointer address natural
  have data := data_le_base input contents
  have positive := base_positive input contents
  have square := base_le_square input contents
  unfold Log.HeapRelease.clearBudget
  nlinarith

end PDROC.BitVM.VM.ISA.HeapResources
