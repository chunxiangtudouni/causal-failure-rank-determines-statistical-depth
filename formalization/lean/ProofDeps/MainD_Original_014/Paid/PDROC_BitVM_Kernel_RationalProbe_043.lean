module

public import Paid.PDROC_BitVM_Kernel_Branch_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RationalProbe

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal
open PaperProofs.Common.Native.RationalControllerComputation

def natZeroPrefix (word : List Bool) : Bool :=
  decide ((word.head?,word.tail.head?,word.tail.tail.head?)=(some true,some false,some false))

theorem prefix_three (word : List Bool)
    (observed : (word.head?,word.tail.head?,word.tail.tail.head?)=(some true,some false,some false)) :
    ∃ suffix,word=[true,false,false]++suffix := by
  cases word with
  | nil => cases observed
  | cons a rest =>
    cases rest with
    | nil => cases observed
    | cons b rest =>
      cases rest with
      | nil => cases observed
      | cons c rest =>
        have sameA : a=true := Option.some.inj (congrArg Prod.fst observed)
        have sameB : b=false := Option.some.inj (congrArg (fun value=>value.2.1) observed)
        have sameC : c=false := Option.some.inj (congrArg (fun value=>value.2.2) observed)
        subst a
        subst b
        subst c
        exact ⟨rest,rfl⟩

/-- The zero test is prefix decoding of the real self-delimiting word.
No width or Nat comparison is evaluated by the finite bit inspector. -/
theorem natural_zero (value : ℕ) (suffix : List Bool) :
    natZeroPrefix (encodeNatBits value++suffix)=decide (value=0) := by
  have equivalent : ((encodeNatBits value++suffix).head?,(encodeNatBits value++suffix).tail.head?,
      (encodeNatBits value++suffix).tail.tail.head?)=(some true,some false,some false) ↔ value=0 := by
    constructor
    · intro observed
      obtain ⟨tail,same⟩ := prefix_three (encodeNatBits value++suffix) observed
      have encoded : encodeNat 0++tail=encodeNat value++suffix := same.symm
      exact (PSTRTMCodec001.encodeNat_prefix 0 value tail suffix encoded).1.symm
    · intro same
      subst value
      rfl
  simp only [natZeroPrefix,equivalent]

def zeroFlag (store : Branch.Store) : Bool :=
  decide ((store.2.2.1,store.2.2.2.1,store.2.2.2.2)=(some true,some false,some false))

theorem rational_zero (value : Rat) (suffix : List Bool) :
    zeroFlag (Branch.captured (encodeCellBits (.rational value)++suffix))=decide (value=0) := by
  have same := natural_zero value.num.natAbs (encodeNatBits value.den++suffix)
  simpa only [zeroFlag,Branch.captured,encodeCellBits,List.append_assoc,List.cons_append,List.nil_append,
    List.head?_cons,List.tail_cons,natZeroPrefix,Int.natAbs_eq_zero,Rat.num_eq_zero] using same

theorem rational_sign (value : Rat) (suffix : List Bool) :
    Branch.negativeFlag (Branch.captured (encodeCellBits (.rational value)++suffix))=decide (value<0) := by
  simp [Branch.negativeFlag,Branch.captured,encodeCellBits]

/-- The existing five-pop/five-restore program reads the ACTUAL result
Cell on work0. Both flags and complete physical restoration refer to its
one selected run; the rational value is only a proof description. -/
theorem runs (value : Rat) (suffix : List Bool) (contents : Stack → List Bool) (store : Branch.Store)
    (input : contents 0=encodeCellBits (.rational value)++suffix) :
    ∃ (run : List Branch.State) (final : Branch.State),
      run.head?=some (⟨some (),store,contents⟩ : Branch.State) ∧
      run.IsChain (fun a b=>TM2.step (Branch.program 0) a=some b) ∧
      run.getLast?=some final ∧ TM2.step (Branch.program 0) final=none ∧
      final.stk=contents ∧ zeroFlag final.var=decide (value=0) ∧
      Branch.negativeFlag final.var=decide (value<0) ∧ run.length=2 := by
  obtain ⟨run,head,chain,last,halt,time⟩ := Branch.runs 0 contents store
  refine ⟨run,⟨none,Branch.captured (contents 0),contents⟩,head,chain,last,halt,rfl,?_,?_,time⟩
  · rw [input]
    exact rational_zero value suffix
  · rw [input]
    exact rational_sign value suffix

end PDROC.BitVM.Kernel.RationalProbe
