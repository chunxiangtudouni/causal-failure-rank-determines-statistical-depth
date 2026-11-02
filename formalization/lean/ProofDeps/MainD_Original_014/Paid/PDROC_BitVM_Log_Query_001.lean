module

public import Paid.PDROC_BitVM_Log_TM2_002
public import Paid.PDROC_BitVM_Native_Inline_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Literal word comparison, before its real trace proof. Address/query are
Bool-stack words, never Nat values in sigma. The machine's only equality test
is equality of two Option Bool symbols. Fixed stack/return translations reuse
Native.Lift/Inline instead of supplying a second generic lifting library. -/

namespace PDROC.BitVM.Log.Query

open Turing

abbrev Stack := Fin 7
abbrev Label := Fin 4
abbrev Alphabet (_ : Stack) := Bool
abbrev Extra := Option Bool × (Bool × Bool)
abbrev Store := Option Bool × Extra
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

/-- Extra fields are last query symbol, equality flag, original record tag. -/
def querySymbol (store : Store) : Option Bool := store.2.1
def equality (store : Store) : Bool := store.2.2.1
def recordTag (store : Store) : Bool := store.2.2.2

def setRecord (store : Store) (symbol : Option Bool) : Store := (symbol, store.2)
def setQuery (store : Store) (symbol : Option Bool) : Store :=
  (store.1, (symbol, store.2.2))
def setEquality (store : Store) (flag : Bool) : Store :=
  (store.1, (store.2.1, (flag, store.2.2.2)))

def compareSymbol (store : Store) : Store :=
  setEquality store (equality store && decide (store.1 = querySymbol store))

def compareEnd (store : Store) : Store :=
  setEquality store (equality store && !(querySymbol store).isSome)

def compareCode : Statement :=
  .pop 1 setRecord
    (.branch (fun store => store.1.isSome)
      (.pop 3 setQuery
        (.branch (fun store => (querySymbol store).isSome)
          (.push 4 (fun store => (querySymbol store).getD false)
            (.load compareSymbol (.goto (fun _ => 1))))
          (.load compareSymbol (.goto (fun _ => 1)))))
      (.peek 3 setQuery (.load compareEnd (.goto (fun _ => 2)))))

def restoreEmbed : TwoStack.Stack ↪ Stack where
  toFun := fun stack => if stack = 0 then 4 else if stack = 1 then 3 else 5
  inj' := by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all

def localDrain (_ : TwoStack.Label) : TwoStack.Statement := TwoStack.drain 0 1 0 .halt

/-- Archive4→query3 with a real return to3; all other stacks/flags frame. -/
def restoreCode : Statement :=
  Native.Inline.statement (τ := Extra) (fun _ : TwoStack.Label => (2 : Label)) 3
    (Native.Lift.statement restoreEmbed (localDrain 0))

def program (label : Label) : Statement :=
  if label = 0 then .load (fun store => setEquality store true) (.goto (fun _ => 1))
  else if label = 1 then compareCode
  else if label = 2 then restoreCode
  else .halt

theorem initialize_step (contents : Stack → List Bool) (store : Store) :
    TM2.step program (⟨some 0, store, contents⟩ : State) =
      some (⟨some 1, setEquality store true, contents⟩ : State) := rfl

theorem final_halt (contents : Stack → List Bool) (store : Store) :
    TM2.step program (⟨some 3, store, contents⟩ : State) =
      some (⟨none, store, contents⟩ : State) := rfl

theorem final_halted (contents : Stack → List Bool) (store : Store) :
    TM2.step program (⟨none, store, contents⟩ : State) = none := rfl

theorem restore_supports : TM2.SupportsStmt (Finset.univ : Finset Label) restoreCode := by
  apply Native.Inline.supports_statement
    (fun _ : TwoStack.Label => (2 : Label)) 3 (Finset.univ : Finset TwoStack.Label)
    (Finset.univ : Finset Label)
  · intro label _; exact Finset.mem_univ _
  · exact Finset.mem_univ _
  · apply Native.Lift.supports_statement
    simp [localDrain, TwoStack.drain, TM2.SupportsStmt]

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · simp [program, TM2.SupportsStmt]
    · simp [program, compareCode, TM2.SupportsStmt]
    · simpa [program] using restore_supports
    · simp [program, TM2.SupportsStmt]

end PDROC.BitVM.Log.Query
