module
public import RootB235_ArchiveStaging_Data010
public import RootB235_ArchiveStaging_Unary_Count001

/-! Fixed original paired archive -> exact staged raw tape producer.
All Datum tags, length prefixes, original count payloads, work disposal,
output cells and head movement belong to one actual finite Bool TM0 path.
The gap is exactly zero; no host-generated raw answer enters the program. -/
@[expose] public section
set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
open Turing RationalControllerComputation RationalControllerComputation.PSTRTMSeq005
open RationalControllerComputation.PSTRSymbolicLaneArchive
open RationalControllerComputation.PSTRSymbolicLaneScan
open RationalControllerComputation.PSTRSymbolicCursorArchive
open RationalControllerComputation.PSTRSymbolicRawLoop
open RationalControllerComputation.PSTRTMRawNat010
open RationalControllerComputation.PSTRSymbolicRelabel

namespace Producer

def setupInput (root : List Bool) (data : List Datum) : Tape Bool :=
  Tape.mk₂ ((navigationCells (allDatumPairs data)).reverse++false::true::root) [true]

def setup (root : List Bool) (data : List Datum) :
    Segment Control.code ⟨.entry,setupInput root data⟩
      (Control.state 0 (DataLoop.cursor root data [] [] 0)) 28 := by
  let west := (navigationCells (allDatumPairs data)).reverse++false::true::root
  let a : TM0.Cfg Bool Control.Label := ⟨.entry,setupInput root data⟩
  let b : TM0.Cfg Bool Control.Label := ⟨.boot 2,setupInput root data⟩
  let c : TM0.Cfg Bool Control.Label :=
    ⟨.boot 15,(Tape.mk₂ west [true,false,true,true,true]).move .left⟩
  let d := Control.state 0 (DataLoop.cursor root data [] [] 0)
  have ab : TM0.step Control.code a=some b := by
    simp [a,b,Control.code,TM0.step,Tape.write_self]
  have middle : Segment Control.code b c 24 :=
    call_map_segment Control.code Terminal.stageMachine Control.Label.boot
      (fun _ => Control.Label.control (.at 0)) (by intro q bit;rfl) (Terminal.fixedFooter west)
  have cd : TM0.step Control.code c=some d := by
    simp only [c,d,Control.state,DataLoop.cursor,Macro.suffix,MarkSeek.pairs,PairPrepend.word,
      List.flatMap_nil,List.nil_append,List.replicate_zero,Control.code,call,Terminal.stageMachine,
      TM0.step,Option.map_some,Tape.write_self]
    rfl
  exact ((Segment.edge ab).trans middle).trans (Segment.edge cd)

noncomputable def terminalRun (higher output : List Bool) :
    Segment Control.code ⟨.terminal 0,Terminal.sourceTape higher output 0⟩
      ⟨.done,ReverseLoop.tape output.reverse [] 0 []⟩ (3*higher.length+4*output.length+42) := by
  let result := Terminal.actual higher output 0 0
  let path := Classical.choose result
  let final := Classical.choose (Classical.choose_spec result)
  have spec := Classical.choose_spec (Classical.choose_spec result)
  obtain ⟨run,_port,tape,time,_space⟩ := spec
  have called := call_segment Control.code Terminal.machine Control.Label.terminal
    (fun _ => Control.Label.done) (by intro q bit;rfl) _ _ path run.1 run.2.1 run.2.2.1 run.2.2.2
  change final.Tape=ReverseLoop.tape output.reverse [] 0 [] at tape
  change path.length≤3*higher.length+0+4*output.length+40 at time
  rw [tape] at called
  exact called.weaken (by omega)

noncomputable def symbolic (data : List Datum) (work : List Bool)
    (width : 2≤work.length)
    (workRoom : work.length≤(PSTRTMNatValue017.rawPayload data.length).length+1) :
    Segment Control.code
      ⟨.entry,archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) work [] true⟩
      ⟨.done,StagedFin16.stagedTape data 0⟩ (10000000*((encode data).length+1)^3) := by
  let original := PSTRTMNatValue017.rawPayload data.length
  let size := (encode data).length
  let payload := data.flatMap encodeDatum
  let cleaned := DataLoop.clean data
  have originalNonempty : original≠[] := rawPayload_nonempty data.length
  have layout : size=2*original.length+2+payload.length := by
    simp only [size,original,payload,encode,List.length_append,PSTRTMLength004.encodeNat_length,
      List.length_singleton,PSTRTMNatValue017.rawPayload,List.length_ofFn]
    omega
  have pairs := pairs_bytes data
  have count := count_bytes data
  change 2*(allDatumPairs data).length=payload.length at pairs
  change data.length≤payload.length at count
  change work.length≤original.length+1 at workRoom
  have cleanedLength : cleaned.length=(allDatumPairs data).length := DataLoop.clean_length data
  have payloadRoom : payload.length≤size := by omega
  have pairRoom : (allDatumPairs data).length≤size := by omega
  have countRoom : data.length≤size := by omega
  have originalRoom : original.length≤size := by omega
  have workBound : work.length≤size+1 := by omega
  cases workShape : work.reverse with
  | nil =>
    have sizes := congrArg List.length workShape
    simp only [List.length_reverse,List.length_nil] at sizes
    omega
  | cons first rest =>
    let root := first::(leftBlocks rest++false::false::HeaderCopy.bank original)
    have header : leftBlocks work.reverse++false::false::HeaderCopy.bank original=true::root := by
      simp only [workShape,leftBlocks,List.flatMap_cons,List.cons_append,List.nil_append,root]
    have inputEq : archiveTape data (false::HeaderCopy.bank original) work [] true=setupInput root data := by
      simp only [archiveTape,setupInput,header]
    have front := setup root data
    rw [←inputEq] at front
    have parsed := DataLoop.actual root data [] [] 0 size (by simpa using pairRoom)
      (by simpa only [List.length_nil,Nat.add_zero] using payloadRoom) (Nat.zero_le size)
    simp only [List.append_nil] at parsed
    have afterData : DataLoop.cursor root [] cleaned payload 0=(CountPrepare.input original work cleaned payload 0).Tape := by
      simp only [DataLoop.cursor,allDatumPairs,List.flatMap_nil,navigationCells,List.reverse_nil,
        List.nil_append,CountPrepare.input,Control.state,header,Tape.mk₂]
      simp
    rw [afterData] at parsed
    have prepared := CountPrepare.actual original work cleaned payload 0 originalNonempty width
    let countHigher := List.replicate (work.length+1) false++cleaned
    let endHigher := List.replicate (original.length+1) false++countHigher
    have counted := Control.fieldRun 94 3 rfl rfl [] countHigher payload false 0 original
    have rawOutput : List.replicate original.length true++false::(original++payload)=rawPrefix data := by
      rw [rawPrefix,←DataLoop.word_raw data.length]
      simp only [original,payload,Rational.numberWord,List.append_assoc,List.cons_append]
    have countedEnd : (NumberField.finish [] countHigher payload false 0 original).Tape=
        Macro.source [] endHigher (rawPrefix data) true false 0 := by
      simp only [NumberField.finish,NumberField.cfg,Macro.cfg,rawOutput,endHigher]
    rw [countedEnd] at counted
    let a := Control.cfg 95 [] endHigher (rawPrefix data) true false 0
    let b := Control.cfg 96 [] endHigher (rawPrefix data) true true 0
    have boundary : Segment Control.code a b 3 := by
      apply follow_actual Control.code 1
      simp [a,b,Control.cfg,Control.state,Macro.source,follow,Control.code,call,Macro.code,
        Control.program,TM0.step,Tape.mk₂]
    have terminalEntry : TM0.step Control.code b=some ⟨.terminal 0,Terminal.sourceTape endHigher (rawPrefix data) 0⟩ := by
      simp only [b,Control.cfg,Control.state,Control.code,call,Macro.code,Control.program,TM0.step,
        Option.map_some,Tape.write_self,Control.controlFinish]
      rfl
    have terminal := terminalRun endHigher (rawPrefix data)
    have whole := (((((front.trans parsed).trans prepared).trans counted).trans boundary).trans
      (Segment.edge terminalEntry)).trans terminal
    have countArgs : original.length+countHigher.length+payload.length+0+1≤4*size+3 := by
      simp only [countHigher,List.length_append,List.length_replicate]
      omega
    have countedTime : 1000*(original.length+countHigher.length+payload.length+0+1)^2≤25000*(size+1)^2 := by
      have square := Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left countArgs 2)
      exact square.trans (by nlinarith [Nat.zero_le (size^2)])
    have prepTime : 100*(work.length+original.length+1)≤200*(size+1) := by omega
    have higherRoom : endHigher.length≤3*size+3 := by
      simp only [endHigher,countHigher,List.length_append,List.length_replicate]
      omega
    have rawRoom : (rawPrefix data).length≤size := by
      have bytes := raw_input_length data
      omega
    have terminalTime : 3*endHigher.length+4*(rawPrefix data).length+42≤13*size+51 := by omega
    have dataTime : data.length*DataLoop.budget size≤size*DataLoop.budget size :=
      Nat.mul_le_mul_right (DataLoop.budget size) countRoom
    have bound : 28+(data.length*DataLoop.budget size+1)+100*(work.length+original.length+1)+
          (1000*(original.length+countHigher.length+payload.length+0+1)^2+4)+3+2+
          (3*endHigher.length+4*(rawPrefix data).length+42)≤10000000*(size+1)^3 := by
      unfold DataLoop.budget at dataTime ⊢
      nlinarith only [dataTime,countedTime,prepTime,terminalTime,Nat.zero_le (size^2),Nat.zero_le (size^3)]
    simpa only [StagedFin16.stagedTape,size,original] using whole.weaken bound

theorem actual (data : List Datum) (work : List Bool)
    (width : 2≤work.length)
    (workRoom : work.length≤(PSTRTMNatValue017.rawPayload data.length).length+1) :
    ∃ path final, RunsFrom Control.machine
        ⟨0,archiveTape data (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) work [] true⟩ path final ∧
      final.q=Control.haltPort ∧ final.Tape=StagedFin16.stagedTape data 0 ∧
      path.length≤10000000*((encode data).length+1)^3 ∧ ∀ clock,
        visitedSpace Control.machine (encode data).length (path.take clock)≤
          30000000*((encode data).length+1)^3 := by
  classical
  let source := symbolic data work width workRoom
  let labels := finiteLabels Control.support
  let lift : TM0.Cfg Bool Control.Label → MachineState Control.support.card := relabelCfg labels
  let path := source.trace.map lift
  let final := lift ⟨.done,StagedFin16.stagedTape data 0⟩
  have step (cfg : TM0.Cfg Bool Control.Label) :
      TM0.step Control.machine (lift cfg)=(TM0.step Control.code cfg).map lift :=
    (relabel_step Control.code (Control.support : Set Control.Label) labels (finiteDecode Control.support)
      (finite_inverse Control.support) cfg (Finset.mem_univ _)).symm
  have entry : labels (.entry)=0 := by
    change finiteLabels Control.support default=0
    simp [finiteLabels]
  have head : path.head?=some (⟨0,archiveTape data
      (false::HeaderCopy.bank (PSTRTMNatValue017.rawPayload data.length)) work [] true⟩ : MachineState Control.support.card) := by
    simp only [path,List.head?_map,source.head,Option.map_some,lift,relabelCfg,entry]
  have chain : path.IsChain (fun a b => TM0.step Control.machine a=some b) :=
    (List.isChain_map _).mpr (source.chain.imp (fun a b edge => by rw [step,edge];rfl))
  have last : path.getLast?=some final := by
    simp only [path,List.getLast?_map,source.tail,Option.map_some,final]
  have halt : TM0.step Control.machine final=none := by
    rw [step]
    simp [Control.code,TM0.step]
  have time : path.length≤10000000*((encode data).length+1)^3 := by
    simpa only [path,List.length_map] using source.time
  refine ⟨path,final,⟨head,chain,last,halt⟩,rfl,rfl,time,?_⟩
  intro clock
  have cells := PSTRTMTrace002.visitedSpace_le Control.machine (encode data).length (path.take clock)
  have take := (List.length_take_le' clock path).trans time
  nlinarith only [cells,take,Nat.zero_le ((encode data).length^2),Nat.zero_le ((encode data).length^3)]

end Producer
end PaperProofs.Common.Native.PSTRWordBool.RawInit.B23_5.ArchiveStaging
