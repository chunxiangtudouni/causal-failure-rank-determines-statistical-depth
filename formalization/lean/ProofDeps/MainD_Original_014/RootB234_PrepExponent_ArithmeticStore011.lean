module

public import RootB234_PrepExponent_NatToRatPublic008
public import B23_4_RatWordPrep_SeqCmp_FullStore_110
public import RootB234_RuntimeCounter_Round_Public_007
public import PSTR_WordBool_RatCmp_Code_001

/-! The fixed finite stores used by the global exponent source. Product
reindexing is static; no arithmetic call resets another callee's memory. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Arithmetic
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM

abbrev MulAux := RatBinary.Store Unit RatMulDiv.mulStates
abbrev SubAux := RatBinary.Store Unit RatAddSub.addSubStates
abbrev RoundAux := RuntimeCounter.Round.Registers
abbrev ReaderAux := RatCmp.Reader.Store
abbrev Aux := ((MulAux×SubAux)×RoundAux)×ReaderAux
abbrev Base (C : Type*) := C×RatOutput.Store
abbrev Store (C : Type*) := Aux×Base C

abbrev PacketContext (C : Type*) := Aux×C
abbrev MulContext (C : Type*) := ((SubAux×RoundAux)×ReaderAux)×Base C
abbrev SubContext (C : Type*) := ((MulAux×RoundAux)×ReaderAux)×Base C
abbrev RoundContext (C : Type*) := ((MulAux×SubAux)×ReaderAux)×Base C
abbrev ReaderContext (C : Type*) := ((MulAux×SubAux)×RoundAux)×Base C

def packetIso (C : Type*) : (PacketContext C×RatOutput.Store) ≃ Store C :=
  Equiv.prodAssoc Aux C RatOutput.Store

def mulPlace (C : Type*) : (MulContext C×MulAux) ≃ Store C where
  toFun := fun v => ((((v.2,v.1.1.1.1),v.1.1.1.2),v.1.1.2),v.1.2)
  invFun := fun v => ((((v.1.1.1.2,v.1.1.2),v.1.2),v.2),v.1.1.1.1)
  left_inv := by rintro ⟨⟨⟨⟨sub,round⟩,reader⟩,base⟩,mul⟩;rfl
  right_inv := by rintro ⟨⟨⟨⟨mul,sub⟩,round⟩,reader⟩,base⟩;rfl

def subPlace (C : Type*) : (SubContext C×SubAux) ≃ Store C where
  toFun := fun v => ((((v.1.1.1.1,v.2),v.1.1.1.2),v.1.1.2),v.1.2)
  invFun := fun v => ((((v.1.1.1.1,v.1.1.2),v.1.2),v.2),v.1.1.1.2)
  left_inv := by rintro ⟨⟨⟨⟨mul,round⟩,reader⟩,base⟩,sub⟩;rfl
  right_inv := by rintro ⟨⟨⟨⟨mul,sub⟩,round⟩,reader⟩,base⟩;rfl

def roundPlace (C : Type*) : (RoundContext C×RoundAux) ≃ Store C where
  toFun := fun v => (((v.1.1.1,v.2),v.1.1.2),v.1.2)
  invFun := fun v => (((v.1.1.1,v.1.2),v.2),v.1.1.2)
  left_inv := by rintro ⟨⟨⟨pair,reader⟩,base⟩,round⟩;rfl
  right_inv := by rintro ⟨⟨⟨pair,round⟩,reader⟩,base⟩;rfl

def readerPlace (C : Type*) : (ReaderContext C×ReaderAux) ≃ Store C :=
  StoreIso.exchange ((MulAux×SubAux)×RoundAux) (Base C) ReaderAux

def mulIso (C : Type*) : RatBinary.Store (MulContext C) RatMulDiv.mulStates ≃ Store C :=
  (B23_4_RatWordPrep.FullStore.binaryFlat (MulContext C) RatMulDiv.mulStates).trans (mulPlace C)

def subIso (C : Type*) : RatBinary.Store (SubContext C) RatAddSub.addSubStates ≃ Store C :=
  (B23_4_RatWordPrep.FullStore.binaryFlat (SubContext C) RatAddSub.addSubStates).trans (subPlace C)

def roundIso (C : Type*) : RuntimeCounter.Round.Store (RoundContext C) ≃ Store C := roundPlace C

def readerIso (C : Type*) : (ReaderContext C×ReaderAux) ≃ Store C := readerPlace C

def binaryRoles : RatInput.Stack ≃ RatInput.Stack := (Equiv.swap 8 2).trans (Equiv.swap 9 10)

def Work (slot : RatInput.Stack) : Prop := RatPair.Link.Work (binaryRoles.symm slot)

instance (slot : RatInput.Stack) : Decidable (Work slot) := by
  unfold Work RatPair.Link.Work
  infer_instance

theorem frame_roles :
    (∀ slot : RatInput.Stack,slot=0 ∨ slot=1 ∨ slot=8 ∨ slot=9 ∨ slot=11→¬Work slot) := by
  intro slot framed
  rcases framed with rfl|rfl|rfl|rfl|rfl <;> decide

theorem scratch_role : binaryRoles 7=7 := rfl
theorem source_role : binaryRoles 15=15 := rfl

theorem mul_context (C : Type*) (v : RatBinary.Store (MulContext C) RatMulDiv.mulStates) :
    (mulIso C v).2.1=v.1.1.1.1.1.2.1 := rfl

theorem sub_context (C : Type*) (v : RatBinary.Store (SubContext C) RatAddSub.addSubStates) :
    (subIso C v).2.1=v.1.1.1.1.1.2.1 := rfl

theorem finite_store (C : Type*) [Finite C] : Finite (Store C) := inferInstance

end RootB234.PrepExponent.Arithmetic
