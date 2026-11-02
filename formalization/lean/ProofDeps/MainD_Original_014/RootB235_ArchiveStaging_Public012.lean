module
public import RootB235_ArchiveStaging_Producer011

/-! Normal-import public producer endpoint. The machine and HALT are fixed
before every original data list and every internally produced work bank. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging.Public
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicCursorArchive

noncomputable def machine : Machine Control.support.card := Control.machine
noncomputable def haltPort : Fin (Control.support.card+1) := Control.haltPort

theorem actual (data : List Datum) (work : List Bool)
    (width : 2≤work.length)
    (workRoom : work.length≤(PSTRTMNatValue017.rawPayload data.length).length+1) :
    ∃ path final, RunsFrom machine
        ⟨0,archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) work [] true⟩ path final ∧
      final.q=haltPort ∧ final.Tape=StagedFin16.stagedTape data 0 ∧
      path.length≤10000000*((encode data).length+1)^3 ∧ ∀ clock,
        visitedSpace machine (encode data).length (path.take clock)≤30000000*((encode data).length+1)^3 :=
  Producer.actual data work width workRoom

theorem fixed_producer : ∃ (states : Nat) (program : Machine states) (halt : Fin (states+1)),
    ∀ (data : List Datum) (work : List Bool), 2≤work.length →
      work.length≤(PSTRTMNatValue017.rawPayload data.length).length+1 →
      ∃ path final, RunsFrom program
          ⟨0,archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) work [] true⟩ path final ∧
        final.q=halt ∧ final.Tape=StagedFin16.stagedTape data 0 ∧
        path.length≤10000000*((encode data).length+1)^3 ∧ ∀ clock,
          visitedSpace program (encode data).length (path.take clock)≤30000000*((encode data).length+1)^3 :=
  ⟨Control.support.card,machine,haltPort,actual⟩

end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging.Public
