module

public import Paid.PDCompute_CoreEmit_OutputSlot_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.CoreEmit
open PaperProofs.Paid.Computation

theorem emitted_extend (before state : State) (emitted later : List Cell)
    (emittedProof : RootD27.Core.EmittedPrefix before emitted state) :
    RootD27.Core.EmittedPrefix before (emitted++later) state := by
  obtain ⟨heap,live,written,pending,decomposition,output⟩:=emittedProof
  exact ⟨heap,live,written,pending++later,by rw [decomposition,List.append_assoc],output⟩

theorem emitted_prepend (before middle state : State) (earlier emitted : List Cell)
    (heap : middle.heap=before.heap) (live : middle.live=before.live)
    (output : middle.output=before.output++earlier)
    (emittedProof : RootD27.Core.EmittedPrefix middle emitted state) :
    RootD27.Core.EmittedPrefix before (earlier++emitted) state := by
  obtain ⟨laterHeap,laterLive,written,pending,decomposition,laterOutput⟩:=emittedProof
  refine ⟨laterHeap.trans heap,laterLive.trans live,earlier++written,pending,?_,?_⟩
  · rw [decomposition,List.append_assoc]
  · rw [laterOutput,output,List.append_assoc]

end PDCompute.CoreEmit
