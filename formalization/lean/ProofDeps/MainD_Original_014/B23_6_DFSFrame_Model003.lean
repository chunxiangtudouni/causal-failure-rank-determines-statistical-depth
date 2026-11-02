module
public import B23_6_DFSFrame_Code001

/-! Physical codec and exact saved-spool footprint. These model functions are
used only in specifications/proofs; the finite source never evaluates them. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true
namespace B23_6.DFSFrame
open PaperProofs.Common.Native.PSTRWordBool
variable {C : Type*}

def pairs (bits : List Bool) : List Bool := bits.flatMap (fun bit => [true,bit])
def code (bits : List Bool) : List Bool := pairs bits.reverse++[false,false]

theorem pairs_nil : pairs []=[] := rfl
theorem pairs_cons (bit : Bool) (bits : List Bool) : pairs (bit::bits)=true::bit::pairs bits := rfl
theorem pairs_append (a b : List Bool) : pairs (a++b)=pairs a++pairs b := List.flatMap_append
theorem pairs_length (bits : List Bool) : (pairs bits).length=2*bits.length := by
  induction bits with
  | nil => rfl
  | cons bit bits ih => simp only [pairs_cons,List.length_cons,ih];omega
theorem code_length (bits : List Bool) : (code bits).length=2*bits.length+2 := by
  simp only [code,List.length_append,pairs_length,List.length_reverse,List.length_cons,List.length_nil]
theorem pairs_reverse_cons (bit : Bool) (bits tail : List Bool) :
    pairs (bit::bits).reverse++tail=pairs bits.reverse++true::bit::tail := by
  simp only [List.reverse_cons,pairs_append,pairs_cons,pairs_nil,List.nil_append,List.append_assoc,List.cons_append]

def rom (n : Nat) : Field := ⟨n%14,Nat.mod_lt n (by decide)⟩
def position (n : Nat) : Fin 15 := ⟨n%15,Nat.mod_lt n (by decide)⟩
def index (slot : Stack) : Nat := if slot=14 then 13 else slot.val
def seedSlot (slot : Stack) : Bool := decide (slot=0 ∨ slot=1 ∨ slot=2 ∨ slot=4 ∨ slot=11)

theorem rom_val (n : Nat) (small : n<14) : (rom n).val=n := Nat.mod_eq_of_lt small
theorem position_val (n : Nat) (small : n<15) : (position n).val=n := Nat.mod_eq_of_lt small
theorem rom_index (i : Field) : rom i.val=i := Fin.ext (Nat.mod_eq_of_lt i.isLt)
theorem field_index (i : Field) : index (field i)=i.val := by
  fin_cases i <;> rfl
theorem index_small (slot : Stack) (not13 : slot≠13) (not15 : slot≠15) : index slot<14 := by
  fin_cases slot <;> simp_all [index]
theorem field_index_inverse (slot : Stack) (not13 : slot≠13) (not15 : slot≠15) :
    field (rom (index slot))=slot := by
  fin_cases slot <;> simp_all [field,rom,index]
theorem index_equal (i : Field) (slot : Stack) (not13 : slot≠13) (not15 : slot≠15)
    (equal : index slot=i.val) : slot=field i := by
  rw [←field_index_inverse slot not13 not15,equal,rom_index]
theorem seed_field (i : Field) : seedSlot (field i)=seed i := rfl

def framePrefix (parent : Bank) (kind : Bool) : Nat → List Bool
  | 0 => kind::parent 13
  | n+1 => code (parent (field (rom n)))++framePrefix parent kind n
def massPrefix (parent : Bank) : Nat → Nat
  | 0 => 0
  | n+1 => (parent (field (rom n))).length+massPrefix parent n

def prefixBank (parent : Bank) (kind : Bool) (n : Nat) : Bank := fun slot =>
  if slot=13 then framePrefix parent kind n else if slot=15 then [] else
  if index slot<n ∧ seedSlot slot=false then [] else parent slot

def saveOne (i : Field) (before : Bank) : Bank :=
  Function.update (Function.update (Function.update before 13 (code (before (field i))++before 13))
    (field i) (if seed i then before (field i) else [])) 15 []
def pushBank (kind : Bool) (parent : Bank) : Bank :=
  Function.update (prefixBank parent kind 14) 13 (false::framePrefix parent kind 14)
def restoreBank (parent : Bank) (rank : List Bool) : Bank := Function.update parent 15 rank

theorem prefix13 (parent : Bank) (kind : Bool) (n : Nat) : prefixBank parent kind n 13=framePrefix parent kind n := rfl
theorem prefix15 (parent : Bank) (kind : Bool) (n : Nat) : prefixBank parent kind n 15=[] := rfl
theorem prefix_current (parent : Bank) (kind : Bool) (n : Nat) (small : n<14) :
    prefixBank parent kind n (field (rom n))=parent (field (rom n)) := by
  simp only [prefixBank,field_ne13,field_ne15,ite_false,field_index,rom_val n small,lt_self_iff_false,false_and]
theorem prefix_seed (parent : Bank) (kind : Bool) (n : Nat) (slot : Stack)
    (not13 : slot≠13) (not15 : slot≠15) (isSeed : seedSlot slot=true) : prefixBank parent kind n slot=parent slot := by
  simp only [prefixBank,not13,not15,ite_false,isSeed,Bool.true_eq_false,and_false]

theorem prefix_zero (parent : Bank) (kind : Bool) :
    prefixBank parent kind 0=Function.update (Function.update parent 13 (kind::parent 13)) 15 [] := by
  funext slot
  simp only [prefixBank,framePrefix,Nat.not_lt_zero,false_and,ite_false]
  by_cases h13 : slot=13 <;> by_cases h15 : slot=15 <;> simp_all

theorem saveOne_prefix (parent : Bank) (kind : Bool) (n : Nat) (small : n<14) :
    saveOne (rom n) (prefixBank parent kind n)=prefixBank parent kind (n+1) := by
  have rn : (rom n).val=n:=rom_val n small
  funext slot
  by_cases s13 : slot=13
  · subst slot
    simp only [saveOne,Function.update_of_ne (Ne.symm (field_ne13 _)),Function.update_of_ne (by decide : (13 : Stack)≠15),
      Function.update_self,prefix13,prefix_current parent kind n small]
    rfl
  by_cases s15 : slot=15
  · subst slot;simp only [saveOne,Function.update_self,prefix15]
  by_cases sf : slot=field (rom n)
  · subst slot
    simp only [saveOne,Function.update_of_ne (field_ne15 _),Function.update_self,prefix_current parent kind n small]
    simp only [prefixBank,field_ne13,field_ne15,ite_false,field_index,rn,Nat.lt_succ_self,true_and,seed_field]
    cases seed (rom n) <;> simp only [Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  have ine : index slot≠n := by
    intro equal
    exact sf (index_equal (rom n) slot s13 s15 (equal.trans rn.symm))
  have ltiff : index slot<n+1↔index slot<n := by omega
  simp only [saveOne,Function.update_of_ne s15,Function.update_of_ne sf,Function.update_of_ne s13,
    prefixBank,s13,s15,ite_false,ltiff]

theorem frame_length (parent : Bank) (kind : Bool) (n : Nat) :
    (framePrefix parent kind n).length=2*massPrefix parent n+2*n+1+(parent 13).length := by
  induction n with
  | zero => simp only [framePrefix,massPrefix,List.length_cons];omega
  | succ n ih => simp only [framePrefix,massPrefix,List.length_append,code_length,ih];omega
theorem exact_spool (parent : Bank) (kind : Bool) :
    (pushBank kind parent 13).length=(parent 13).length+2*massPrefix parent 14+30 := by
  simp only [pushBank,Function.update_self,List.length_cons,frame_length];omega

theorem massPrefix_bound (parent : Bank) (n : Nat) : massPrefix parent n≤n*RatInput.occupied parent := by
  induction n with
  | zero => simp only [massPrefix,Nat.zero_mul,Nat.le_refl]
  | succ n ih =>
    have room:=RatInput.Encoder.point_mass parent (field (rom n))
    simp only [massPrefix,Nat.succ_mul];omega
theorem massPrefix_mono (parent : Bank) {a b : Nat} (h : a≤b) : massPrefix parent a≤massPrefix parent b := by
  induction h with
  | refl => rfl
  | @step b h ih => exact ih.trans (by simp only [massPrefix];omega)
theorem parent_field_mass (parent : Bank) (i : Field) : (parent (field i)).length≤massPrefix parent 14 := by
  have room : (parent (field (rom i.val))).length≤massPrefix parent (i.val+1) := by
    simp only [massPrefix];omega
  rw [rom_index] at room
  exact room.trans (massPrefix_mono parent (by omega))

end B23_6.DFSFrame
