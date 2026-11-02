module
public import Structure.PA17_TM_RatArithmetic_NativeTail_055b
public import Structure.PA17_TM_Division_Compose_006a

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeTail055

open Turing PA17TMDivisionCompose006 PA17TMRatArithmeticWidth018
open PA17TMRatArithmeticBankWalk033 PA17TMRatArithmeticReturnHome037
open PA17TMRatArithmeticNativeRecord022 PA17TMRatArithmeticNativeCache030
open PA17TMRatArithmeticWideCache045

def tailFamily {states : Nat} (p : Nat) (native : Machine states) (j : Nat)
    (_memory : Fin (p+1)) : Machine (tailCap states j) := nativeTailMachine native j

def tailPorts (p states j : Nat) (_memory : Fin (p+1)) (_local : Fin (tailCap states j+1)) :
    Option (Fin (p+1) × Fin (tailCap states j+1)) := none

def carriedTailCap (p states j : Nat) : Nat := totalStates p (tailCap states j)
attribute [local implicit_reducible] carriedTailCap totalStates tailCap nativeRecordCap

def carriedTailMachine {states : Nat} (p : Nat) (native : Machine states) (j : Nat) :
    Machine (carriedTailCap p states j) :=
  blockMachine (tailFamily p native j) (tailPorts p states j)

def carriedTailEntry (p states j : Nat) (memory : Fin (p+1)) : Fin (carriedTailCap p states j+1) :=
  label memory (0 : Fin (tailCap states j+1))

def carriedTailPort (p states j : Nat) (memory : Fin (p+1)) : Fin (carriedTailCap p states j+1) :=
  label memory (tailPort states j)

theorem carriedTailCap_eq (p states j : Nat) :
    carriedTailCap p states j=(p+1)*(states+13*j+100)-1 := by
  have h : carriedTailCap p states j+1=(p+1)*(states+13*j+100) := by
    simp only [carriedTailCap,totalStates,tailCap_eq]
    ring
  omega

theorem carriedTailEntry_value (p states j : Nat) (memory : Fin (p+1)) :
    (carriedTailEntry p states j memory).val=(tailCap states j+1)*memory.val := by
  simp only [carriedTailEntry,label,Fin.val_zero,Nat.add_zero,Nat.mul_comm]

theorem carriedTailPort_value (p states j : Nat) (memory : Fin (p+1)) :
    (carriedTailPort p states j memory).val=(tailCap states j+1)*memory.val+tailCap states j := by
  simp only [carriedTailPort,label,tailPort_value,Nat.mul_comm]

/-- The old memory row is opaque throughout the actual native call and
return over all records, including its sixth sign bit. -/
theorem carriedTail_contract {states : Nat} (p : Nat) (native : Machine states) (j : Nat)
    (memory : Fin (p+1)) (first : RecordSpec) (later : List RecordSpec) (hj : later.length=j)
    (sx : Bool) (counter nx dx ny dyTail : List Bool) (gap a b value : Nat)
    (actual : WideCacheResult native a b value
      (true::lastArchive sx counter nx dx ny (false::dyTail) first later) gap) :
    ∃ newGap trace, 6≤newGap ∧ newGap≤gap+window a b ∧
      PSTRTMSeq005.RunsFrom (carriedTailMachine p native j)
        ⟨carriedTailEntry p states j memory,tailInput sx counter nx dx ny (false::dyTail) first later gap a b⟩ trace
        ⟨carriedTailPort p states j memory,
          tailOutput sx counter nx dx ny (false::dyTail) first later newGap value⟩ ∧
      trace.length≤tailFee j first later nx dx ny (false::dyTail) newGap a b value ∧
      ∀ prefixLength chargedL, visitedSpace (carriedTailMachine p native j) chargedL
        (trace.take prefixLength)≤chargedL+2*tailFee j first later nx dx ny (false::dyTail) newGap a b value+1 := by
  obtain ⟨newGap,lower,upper,trace,hr,hl⟩ :=
    nativeTail_bounded native j first later hj sx counter nx dx ny dyTail gap a b value actual
  have hh := block_runsFrom (tailFamily p native j) (tailPorts p states j) memory _ _ _ hr rfl
  refine ⟨newGap,trace.map (blockCfg (s:=tailCap states j) memory),lower,upper,?_,?_,?_⟩
  · simpa only [carriedTailMachine,carriedTailEntry,carriedTailPort,blockCfg] using hh
  · simpa only [List.length_map] using hl
  · intro prefixLength chargedL
    have hs := PSTRTMTrace002.visitedSpace_le (carriedTailMachine p native j) chargedL
      ((trace.map (blockCfg (s:=tailCap states j) memory)).take prefixLength)
    have ht : ((trace.map (blockCfg (s:=tailCap states j) memory)).take prefixLength).length≤trace.length := by
      simp only [List.length_take,List.length_map]
      omega
    omega

end PaperProofs.Common.Native.RationalControllerComputation.PA17TMRatArithmeticNativeTail055
