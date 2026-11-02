module

public import Paid.PDROC_BitVM_Kernel_Register_002
public import Paid.PDROC_BitVM_Link_Codec_002
public import Common.PSTR_TM_Codec_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.Branch

open Turing PaperProofs.Paid.Computation
open PDROC.BitVM.Kernel.RegisterGlobal

abbrev Store := Option Bool × Option Bool × Option Bool × Option Bool × Option Bool
abbrev State := TM2.Cfg Alphabet Unit Store
abbrev Statement := TM2.Stmt Alphabet Unit Store

def captured (word : List Bool) : Store :=
  (word.head?,word.tail.head?,word.tail.tail.head?,word.tail.tail.tail.head?,word.tail.tail.tail.tail.head?)

def pushBack (target : Stack) (field : Store → Option Bool) (tail : Statement) : Statement :=
  .branch (fun store=>(field store).isSome)
    (.push target (fun store=>(field store).getD false) tail) tail

/-- Five actual prefix reads and five bounded conditional restores. The
fixed243-state store contains only Option Bool fields; all numeric data and
the remaining word stay on tape. NONE is never restored as a FALSE cell. -/
def program (target : Stack) (_ : Unit) : Statement :=
  .pop target (fun store bit=>(bit,store.2))
    (.pop target (fun store bit=>(store.1,bit,store.2.2))
      (.pop target (fun store bit=>(store.1,store.2.1,bit,store.2.2.2))
        (.pop target (fun store bit=>(store.1,store.2.1,store.2.2.1,bit,store.2.2.2.2))
          (.pop target (fun store bit=>(store.1,store.2.1,store.2.2.1,store.2.2.2.1,bit))
            (pushBack target (fun store=>store.2.2.2.2)
              (pushBack target (fun store=>store.2.2.2.1)
                (pushBack target (fun store=>store.2.2.1)
                  (pushBack target (fun store=>store.2.1)
                    (pushBack target Prod.fst .halt)))))))))

def state (target : Stack) (contents : Stack → List Bool) (label : Option Unit)
    (store : Store) (word : List Bool) : State :=
  ⟨label,store,Function.update contents target word⟩

theorem actual_step (target : Stack) (contents : Stack → List Bool) (word : List Bool) (store : Store) :
    TM2.step (program target) (state target contents (some ()) store word)=
      some (state target contents none (captured word) word) := by
  cases word with
  | nil => simp [program,state,pushBack,captured]
  | cons a rest =>
    cases rest with
    | nil => simp [program,state,pushBack,captured]
    | cons b rest =>
      cases rest with
      | nil => simp [program,state,pushBack,captured]
      | cons c rest =>
        cases rest with
        | nil => simp [program,state,pushBack,captured]
        | cons d rest =>
          cases rest with
          | nil => simp [program,state,pushBack,captured]
          | cons e rest => simp [program,state,pushBack,captured]

def zeroFlag (store : Store) : Bool :=
  decide (store=(some false,some true,some false,some false,none))

def negativeFlag (store : Store) : Bool :=
  decide (store.1=some true ∧ store.2.1=some true)

theorem zero_word (word : List Bool) :
    zeroFlag (captured word)=decide (word=[false,true,false,false]) := by
  cases word with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil => simp [zeroFlag,captured]
    | cons b rest =>
      cases rest with
      | nil => simp [zeroFlag,captured]
      | cons c rest =>
        cases rest with
        | nil => simp [zeroFlag,captured]
        | cons d rest =>
          cases rest with
          | nil => cases a <;> cases b <;> cases c <;> cases d <;> rfl
          | cons e rest => simp [zeroFlag,captured]

theorem natural_zero (value : ℕ) :
    zeroFlag (captured (encodeCellBits (.natural value)))=decide (value=0) := by
  have canonical : encodeCellBits (.natural value)=[false,true,false,false] ↔ value=0 := by
    constructor
    · intro same
      change false::encodeNatBits value=false::encodeNatBits 0 at same
      have words := (List.cons.inj same).2
      apply PaperProofs.Common.Native.RationalControllerComputation.PSTRTMCodec001.encodeNat_injective
      simpa only [PDROC.BitVM.Link.CodecCandidate.encodeNatBits_eq_neutral] using words
    · intro same
      subst value
      rfl
  simpa only [canonical] using zero_word (encodeCellBits (.natural value))

theorem rational_sign (value : ℚ) :
    negativeFlag (captured (encodeCellBits (.rational value)))=decide (value<0) := by
  simp [negativeFlag,captured,encodeCellBits]

/-- A true fixed-control branch inspector with every physical stack
restored byte for byte, even for a short or malformed source word. -/
theorem runs (target : Stack) (contents : Stack → List Bool) (store : Store) :
    ∃ run : List State,
      run.head?=some (⟨some (),store,contents⟩ : State) ∧ 
      run.IsChain (fun a b=>TM2.step (program target) a=some b) ∧ 
      run.getLast?=some (⟨none,captured (contents target),contents⟩ : State) ∧ 
      TM2.step (program target) (⟨none,captured (contents target),contents⟩ : State)=none ∧ 
      run.length=2 := by
  have edge := actual_step target contents (contents target) store
  simp only [state,Function.update_eq_self] at edge
  exact ⟨[⟨some (),store,contents⟩,⟨none,captured (contents target),contents⟩],rfl,
    List.isChain_cons_cons.mpr ⟨edge,List.isChain_singleton _⟩,rfl,rfl,rfl⟩

theorem supports (target : Stack) : TM2.Supports (program target) (Finset.univ : Finset Unit) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    trivial

end PDROC.BitVM.Kernel.Branch
