module

public import Paid.PDLower_CalibrationCompute_Header_006
public import Paid.PDLower_CalibrationCompute_HeapList_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

def savedArguments (state : State) : List Cell :=
  [state.register .old,state.register .address,state.register .total,
   state.register .index,state.register .value]

theorem prologue_heapList (before : State) (base : ℕ) :
    HeapList (prologueResult before base) base (savedArguments before) := by
  apply HeapList.of_values
  · intro index inside
    have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
      simp only [savedArguments,List.length_cons,List.length_nil] at inside
      omega
    rcases alternatives with eq | eq | eq | eq | eq <;> subst index <;>
      simp [prologueResult,storeSlotResult,State.set]
  · intro index inside
    have alternatives : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by
      simp only [savedArguments,List.length_cons,List.length_nil] at inside
      omega
    rcases alternatives with eq | eq | eq | eq | eq <;> subst index <;>
      simp [savedArguments,prologueResult,storeSlotResult,State.set]

theorem savedArguments_typed (P : Parameters) (base endpoints returnPC : ℕ) (before : State)
    (entry : Entry P base endpoints returnPC before) :
    savedArguments before = [.natural returnPC,.natural endpoints,.natural P.certificate.M,
      .natural P.certificate.Q,.rational P.certificate.gamma] := by
  rcases entry with ⟨_,ret,endpoint,M,Q,gamma,_⟩
  simp only [savedArguments,ret,endpoint,M,Q,gamma]

theorem savedArguments_write_later {before : State} {base : ℕ} {arguments : List Cell}
    (represented : HeapList before base arguments) (length : arguments.length = 5)
    (offset : ℕ) (later : 5 ≤ offset) (value : Cell) :
    HeapList (writeCell before (base+offset) value) base arguments := by
  apply HeapList.writeOutside represented
  intro index inside
  rw [length] at inside
  omega

end PDLower.CalibrationCompute
