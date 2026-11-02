module

public import B23_4_RatWordPrep_SeqCmp_WordFoldPaths_118

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFold

open Turing PaperProofs.Statistics
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem lookup_shared (truth : Bool) (before : State C)
    (active : before.l=some (if truth then .trueLookup .boot else .falseLookup .boot)) :
    lookupCfg truth before.var.1 (⟨some .boot,before.var.2,before.stk⟩ : Lookup.State C)=before := by
  cases before with
  | mk point memory slots =>
    change point=some (if truth then .trueLookup .boot else .falseLookup .boot) at active
    subst point
    cases truth <;> rfl

/-- Both arithmetic/output auxiliary blocks are preserved while a lookup
executes on the actual query/table/counter bank. No callee reset occurs. -/
theorem actual_lookup (truth : Bool) (caller : Statement C) (E : BinaryExperiment)
    (symbol : Fin E.alphabetSize) (before : State C) (queryTail metadataTail : List Bool)
    (active : before.l=some (if truth then .trueLookup .boot else .falseLookup .boot))
    (scratch : before.stk 4=[]) (empty13 : before.stk 13=[])
    (query : before.stk 0=NatField.packet symbol.val queryTail)
    (metadata : before.stk 1=NatField.packet E.alphabetSize metadataTail)
    (table : before.stk 2=PacketLists.rats (Channels.channelValues E) []) :
    ∃ (final : State C) (_run : Segment caller before final),
      final.l=some (if truth then .ratio default else .trueLookup .boot) ∧
      final.var.1=before.var.1 ∧ final.var.2.2.2=before.var.2.2.2 ∧
      final.stk 2=before.stk 2 ∧ final.stk 15=RatInput.Encoder.packet (E.channel truth symbol) (before.stk 15) ∧
      final.stk 13=[] ∧ final.stk 4=[] ∧
      ∀ slot,Lookup.LookupFrame slot→final.stk slot=before.stk slot := by
  let oldBefore : Lookup.State C := ⟨some .boot,before.var.2,before.stk⟩
  obtain ⟨oldFinal,oldRun,port,context,unchanged,output,empty13Final,tempFinal,frame⟩ := Lookup.actual_channel truth .halt E symbol
    oldBefore queryTail metadataTail rfl scratch empty13 query metadata table
  have path := lookup_path caller truth before.var.1 oldRun.trace oldBefore oldFinal
    oldRun.first oldRun.chain oldRun.last port
  let final := lookupCfg truth before.var.1 oldFinal
  let run : Segment caller before final :=
    ⟨oldRun.trace.map (lookupCfg truth before.var.1),
      path.1.trans (congrArg some (lookup_shared truth before active)),path.2.1,path.2.2⟩
  refine ⟨final,run,?_,rfl,context,unchanged,output,empty13Final,tempFinal,frame⟩
  change oldFinal.l.map (if truth then trueLabel else falseLabel)=some _
  rw [port]
  cases truth <;> rfl

end B23_4_RatWordPrep.WordFold
