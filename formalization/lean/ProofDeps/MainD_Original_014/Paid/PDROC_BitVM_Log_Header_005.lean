module

public import Paid.PDROC_BitVM_Log_Header_004
public import Paid.PDROC_BitVM_Log_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Log.Header

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

def digits (value : ℕ) : List Bool :=
  List.ofFn (fun position : Fin (natBits value) => value.testBit position.val)

theorem digits_length (value : ℕ) : (digits value).length = natBits value := by
  simp [digits]

theorem natWord_digits (value : ℕ) : natWord (digits value) = encodeNatBits value := by
  simp [natWord, digits, encodeNatBits, List.append_assoc]

theorem initial_eq (input : List Bool) :
    TM2.init (Γ := Alphabet) (Λ := Label) (σ := Store) 0 input =
      state (some 0) none input [] [] := by
  have equal : Function.update (fun _ : Stack => ([] : List Bool)) 0 input = slots input [] [] := by
    funext stack; fin_cases stack <;> simp [slots, TwoStack.stackContents]
  exact congrArg (fun contents : Stack → List Bool => (⟨some 0, none, contents⟩ : State)) equal

/-- The machine above reads the official canonical Nat word, not a host Nat.
The value parameter only specifies which input Bool word this run starts on. -/
theorem officialNat_runs (value : ℕ) (suffix archive : List Bool) (store : Store) :
    ∃ run : List State,
      run.head? = some (state (some 0) store (encodeNatBits value ++ suffix) [] archive) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some (state none none suffix [] ((encodeNatBits value).reverse ++ archive)) ∧
      TM2.step program (state none none suffix [] ((encodeNatBits value).reverse ++ archive)) = none ∧
      run.length = 2 * natBits value + 4 ∧
      (state none none suffix [] ((encodeNatBits value).reverse ++ archive)).stk 0 = suffix ∧
      (state none none suffix [] ((encodeNatBits value).reverse ++ archive)).stk 1 = [] ∧
      (state none none suffix [] ((encodeNatBits value).reverse ++ archive)).stk 2 =
        (encodeNatBits value).reverse ++ archive := by
  simpa only [final, natWord_digits, digits_length] using
    scan_runs (digits value) suffix archive store

/-- The empty-workspace instance starts at genuine TM2.init on the original
Bool word. No counter, width, fuel or precomputed output is supplied as input. -/
theorem officialNat_initial_runs (value : ℕ) (suffix : List Bool) :
    ∃ (run : List State) (after : State),
      run.head? = some (TM2.init (Γ := Alphabet) (Λ := Label) (σ := Store) 0
        (encodeNatBits value ++ suffix)) ∧
      run.IsChain (fun before after => TM2.step program before = some after) ∧
      run.getLast? = some after ∧ TM2.step program after = none ∧
      run.length = 2 * natBits value + 4 ∧
      after.stk 0 = suffix ∧ after.stk 1 = [] ∧ after.stk 2 = (encodeNatBits value).reverse := by
  obtain ⟨run, head, chain, last, halt, size, input, ticks, archive⟩ :=
    officialNat_runs value suffix [] none
  refine ⟨run, state none none suffix [] (encodeNatBits value).reverse,
    ?_, chain, ?_, ?_, size, ?_, ?_, ?_⟩
  · simpa only [initial_eq] using head
  · simpa only [List.append_nil] using last
  · simpa only [List.append_nil] using halt
  · simpa only [List.append_nil] using input
  · simpa only [List.append_nil] using ticks
  · simpa only [List.append_nil] using archive

end PDROC.BitVM.Log.Header
