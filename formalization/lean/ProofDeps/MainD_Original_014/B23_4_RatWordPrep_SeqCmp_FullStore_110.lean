module

public import B23_4_RatWordPrep_SeqCmp_WordPackCode_102
public import B23_4_RatWordPrep_SeqCmp_WordPublic_015
public import PSTR_WordBool_RatBinary_Run_005

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.FullStore

open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open PSTRWordVM

/-- Pure store reindexing. These functions only define static isomorphisms;
the runtime source never resets another callee's registers at a join. -/
def binaryMap {C D : Type*} (states : Nat) (f : C → D) (v : RatBinary.Store C states) : RatBinary.Store D states :=
  (((((f v.1.1.1.1.1,v.1.1.1.1.2),v.1.1.1.2),v.1.1.2),v.1.2),v.2)

def binaryFlat (C : Type*) (states : Nat) : RatBinary.Store C states ≃ C × RatBinary.Store Unit states where
  toFun := fun v => (v.1.1.1.1.1,binaryMap states (fun _ => ()) v)
  invFun := fun v => binaryMap states (fun _ => v.1) v.2
  left_inv := by rintro ⟨⟨⟨⟨⟨context,flags⟩,rat⟩,formatter⟩,native⟩,reader⟩; rfl
  right_inv := by
    rintro ⟨context,⟨⟨⟨⟨⟨unitMemory,flags⟩,rat⟩,formatter⟩,native⟩,reader⟩⟩
    cases unitMemory
    rfl

def wordMap {C D : Type*} (f : C → D) (v : SeqCmp.Word.Store C) : SeqCmp.Word.Store D :=
  (((((((f v.1.1.1.1.1.1.1,v.1.1.1.1.1.1.2),v.1.1.1.1.1.2),v.1.1.1.1.2),v.1.1.1.2),v.1.1.2),v.1.2),v.2)

def wordFlat (C : Type*) : SeqCmp.Word.Store C ≃ C × SeqCmp.Word.Store Unit where
  toFun := fun v => (v.1.1.1.1.1.1.1,wordMap (fun _ => ()) v)
  invFun := fun v => wordMap (fun _ => v.1) v.2
  left_inv := by rintro ⟨⟨⟨⟨⟨⟨⟨context,results⟩,signs⟩,rat⟩,formatter⟩,flags⟩,native⟩,reader⟩; rfl
  right_inv := by
    rintro ⟨context,⟨⟨⟨⟨⟨⟨⟨unitMemory,results⟩,signs⟩,rat⟩,formatter⟩,flags⟩,native⟩,reader⟩⟩
    cases unitMemory
    rfl

abbrev WordAux := SeqCmp.Word.Store Unit
abbrev DivAux := RatBinary.Store Unit RatMulDiv.divStates
abbrev MulAux := RatBinary.Store Unit RatMulDiv.mulStates
abbrev SubAux := RatBinary.Store Unit RatAddSub.addSubStates
abbrev Aux := ((WordAux × DivAux) × MulAux) × SubAux
abbrev Base (C : Type*) := WordPack.Store C
abbrev Store (C : Type*) := Aux × Base C

abbrev WordContext (C : Type*) := ((DivAux × MulAux) × SubAux) × Base C
abbrev DivContext (C : Type*) := ((WordAux × MulAux) × SubAux) × Base C
abbrev MulContext (C : Type*) := ((WordAux × DivAux) × SubAux) × Base C
abbrev SubContext (C : Type*) := ((WordAux × DivAux) × MulAux) × Base C

def wordPlace (C : Type*) : (WordContext C × WordAux) ≃ Store C where
  toFun := fun v => ((((v.2,v.1.1.1.1),v.1.1.1.2),v.1.1.2),v.1.2)
  invFun := fun v => ((((v.1.1.1.2,v.1.1.2),v.1.2),v.2),v.1.1.1.1)
  left_inv := by rintro ⟨⟨⟨⟨divMemory,mulMemory⟩,subMemory⟩,base⟩,wordMemory⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨wordMemory,divMemory⟩,mulMemory⟩,subMemory⟩,base⟩; rfl

def divPlace (C : Type*) : (DivContext C × DivAux) ≃ Store C where
  toFun := fun v => ((((v.1.1.1.1,v.2),v.1.1.1.2),v.1.1.2),v.1.2)
  invFun := fun v => ((((v.1.1.1.1,v.1.1.2),v.1.2),v.2),v.1.1.1.2)
  left_inv := by rintro ⟨⟨⟨⟨wordMemory,mulMemory⟩,subMemory⟩,base⟩,divMemory⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨wordMemory,divMemory⟩,mulMemory⟩,subMemory⟩,base⟩; rfl

def mulPlace (C : Type*) : (MulContext C × MulAux) ≃ Store C where
  toFun := fun v => (((v.1.1.1,v.2),v.1.1.2),v.1.2)
  invFun := fun v => (((v.1.1.1,v.1.2),v.2),v.1.1.2)
  left_inv := by rintro ⟨⟨⟨pair,subMemory⟩,base⟩,mulMemory⟩; rfl
  right_inv := by rintro ⟨⟨⟨pair,mulMemory⟩,subMemory⟩,base⟩; rfl

def subPlace (C : Type*) : (SubContext C × SubAux) ≃ Store C :=
  StoreIso.exchange ((WordAux × DivAux) × MulAux) (Base C) SubAux

def wordIso (C : Type*) : SeqCmp.Word.Store (WordContext C) ≃ Store C :=
  (wordFlat (WordContext C)).trans (wordPlace C)
def divIso (C : Type*) : RatBinary.Store (DivContext C) RatMulDiv.divStates ≃ Store C :=
  (binaryFlat (DivContext C) RatMulDiv.divStates).trans (divPlace C)
def mulIso (C : Type*) : RatBinary.Store (MulContext C) RatMulDiv.mulStates ≃ Store C :=
  (binaryFlat (MulContext C) RatMulDiv.mulStates).trans (mulPlace C)
def subIso (C : Type*) : RatBinary.Store (SubContext C) RatAddSub.addSubStates ≃ Store C :=
  (binaryFlat (SubContext C) RatAddSub.addSubStates).trans (subPlace C)

theorem finite_store (C : Type*) [Fintype C] : Finite (Store C) := by
  let : Fintype WordAux := inferInstance
  let : Fintype DivAux := inferInstance
  let : Fintype MulAux := inferInstance
  let : Fintype SubAux := inferInstance
  let : Fintype (Base C) := inferInstance
  exact inferInstance

end B23_4_RatWordPrep.FullStore
