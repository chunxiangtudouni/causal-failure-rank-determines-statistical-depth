module

public import Paid.PDROC_BitVM_Log_Query_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

/-! Address-field capture for heap lookup. Real header/payload reads archive
each consumed Bool both to historyArchive2 and reverseAddress6. Width is a
Bool tick stack1. The normalization block is the existing genuine drain,
fixed-stack-lifted and returned by the parent libraries. -/

namespace PDROC.BitVM.Log.Capture

open Turing

abbrev Stack := Query.Stack
abbrev Label := Fin 5
abbrev Alphabet (_ : Stack) := Bool
abbrev Store := Query.Store
abbrev State := TM2.Cfg Alphabet Label Store
abbrev Statement := TM2.Stmt Alphabet Label Store

def readHeader : Statement :=
  .pop 0 Query.setRecord
    (.branch (fun store => store.1.isSome)
      (.push 2 (fun store => store.1.getD false)
        (.push 6 (fun store => store.1.getD false)
          (.branch (fun store => store.1.getD false)
            (.push 1 (fun _ => true) (.goto (fun _ => 0)))
            (.goto (fun _ => 1)))))
      (.goto (fun _ => 4)))

def readPayload : Statement :=
  .pop 1 Query.setRecord
    (.branch (fun store => store.1.isSome)
      (.pop 0 Query.setRecord
        (.branch (fun store => store.1.isSome)
          (.push 2 (fun store => store.1.getD false)
            (.push 6 (fun store => store.1.getD false) (.goto (fun _ => 1))))
          (.goto (fun _ => 4))))
      (.goto (fun _ => 2)))

def addressEmbed : TwoStack.Stack ↪ Stack where
  toFun := fun stack => if stack = 0 then 6 else if stack = 1 then 1 else 5
  inj' := by
    intro left right equal
    fin_cases left <;> fin_cases right <;> simp_all

def normalizeCode : Statement :=
  Native.Inline.statement (τ := Query.Extra) (fun _ : TwoStack.Label => (2 : Label)) 3
    (Native.Lift.statement addressEmbed (Query.localDrain 0))

def program (label : Label) : Statement :=
  if label = 0 then readHeader else if label = 1 then readPayload
  else if label = 2 then normalizeCode else .halt

theorem normalize_supports : TM2.SupportsStmt (Finset.univ : Finset Label) normalizeCode := by
  apply Native.Inline.supports_statement
    (fun _ : TwoStack.Label => (2 : Label)) 3 (Finset.univ : Finset TwoStack.Label)
    (Finset.univ : Finset Label)
  · intro label _; exact Finset.mem_univ _
  · exact Finset.mem_univ _
  · apply Native.Lift.supports_statement
    simp [Query.localDrain, TwoStack.drain, TM2.SupportsStmt]

theorem supports : TM2.Supports program (Finset.univ : Finset Label) := by
  constructor
  · exact Finset.mem_univ _
  · intro label _
    fin_cases label
    · simp [program, readHeader, TM2.SupportsStmt]
    · simp [program, readPayload, TM2.SupportsStmt]
    · simpa [program] using normalize_supports
    · simp [program, TM2.SupportsStmt]
    · simp [program, TM2.SupportsStmt]

end PDROC.BitVM.Log.Capture
