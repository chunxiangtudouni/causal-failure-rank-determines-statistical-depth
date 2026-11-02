module

public import Paid.PDCompute_SolverSelectedPointer_079
public import Paid.PDCompute_SolverTestingFields_074

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

def selectedTestingCode (mode : ReaderMode) : List Instruction :=
  selectedPointerCode++scanEndpointCode mode++headerCode testingFieldsCommands

def selectedTestingValues (P : Parameters) (values : ℕ → Cell) (fee penalty : ℚ)
    (previous : MenuRow) (tools source level : ℕ) : ℕ → Cell :=
  let endpoint:=P.cachedEndpoint P.endpointCache level
  let pointed:=Function.update values 39 (.natural (source+(1+2*level)))
  let read:=scanEndpointValues pointed endpoint.error endpoint.charge
  let bad:=P.menuBadBranch fee penalty previous tools
  testingFieldsValues read endpoint.error endpoint.charge (previous.getD tools abandonEntry) bad.2 level
    (if bad.1=.repair then 1 else 0)

/-- A real fixed code sequence reads the actually selected cache pair
and constructs all six ORIGINAL testing-entry working fields. It does
not receive an answer or a precomputed selected entry as machine input. -/
theorem selectedTesting_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools source level : ℕ)
    (before : State) (base n k : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hlevel : values 23=.natural level) (bound : level ≤ P.certificate.M)
    (hgo : values 10=.rational (previous.getD tools abandonEntry).observation)
    (hgr : values 11=.rational (previous.getD tools abandonEntry).repairs)
    (hgf : values 12=.rational (previous.getD tools abandonEntry).failure)
    (hbo : values 31=.rational (P.menuBadBranch fee penalty previous tools).2.observation)
    (hbr : values 32=.rational (P.menuBadBranch fee penalty previous tools).2.repairs)
    (hbf : values 33=.rational (P.menuBadBranch fee penalty previous tools).2.failure)
    (hb : values 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0))
    (fetched : FetchesCode program before.pc (selectedTestingCode mode)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 3120 ∧ Header after base (selectedTestingValues P values fee penalty previous tools source level) ∧
      (List.range 6).map (fun offset => after.heap (base+(40+offset)))=
        denseEncodeEntry (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(selectedTestingCode mode).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let pointed:=selectedPointerResult before base source level
  let pointerValues:=Function.update values 39 (.natural (source+(1+2*level)))
  let endpoint:=P.cachedEndpoint P.endpointCache level
  let readValues:=scanEndpointValues pointerValues endpoint.error endpoint.charge
  have fetchPointer : FetchesCode program before.pc selectedPointerCode := fetched.append_left.append_left
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointerMemory⟩ :=
    selectedPointer_trace_memory program input before base source level values header hbase hsourceValue hlevel fetchPointer
  have pointedHeader : Header pointed base pointerValues := selectedPointerResult_header before base source level values header
  have pointedBase : pointed.register .fresh=.natural base := hbase
  have pointedFrame : Frame before pointed base n k := selectedPointerResult_frame before base source level n k
  have pointedSource:=EndpointSource.frame_of_avoids mode input P source base n k before pointed hsource avoids pointedFrame
  have fetchEndpoint : FetchesCode program pointed.pc (scanEndpointCode mode) := fetched.append_left.append_right
  obtain ⟨readTrace,read,readHead,readLast,readChain,readTime,readHeader,readBase,readPC,readFrame,readOutput,readMemory⟩ :=
    scanEndpointCode_trace_memory mode program input P pointed base source level n k pointerValues pointedHeader pointedBase
      pointedSource bound rfl fetchEndpoint
  have fetchFields : FetchesCode program read.pc (headerCode testingFieldsCommands) := by
    rw [readPC]
    exact fetched.append_right
  have he : readValues 26=.rational endpoint.error := rfl
  have hc : readValues 27=.rational endpoint.charge := rfl
  have hgo' : readValues 10=.rational (previous.getD tools abandonEntry).observation := hgo
  have hgr' : readValues 11=.rational (previous.getD tools abandonEntry).repairs := hgr
  have hgf' : readValues 12=.rational (previous.getD tools abandonEntry).failure := hgf
  have hbo' : readValues 31=.rational (P.menuBadBranch fee penalty previous tools).2.observation := hbo
  have hbr' : readValues 32=.rational (P.menuBadBranch fee penalty previous tools).2.repairs := hbr
  have hbf' : readValues 33=.rational (P.menuBadBranch fee penalty previous tools).2.failure := hbf
  have hl' : readValues 23=.natural level := hlevel
  have hb' : readValues 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0) := hb
  obtain ⟨fieldTrace,after,fieldHead,fieldLast,fieldChain,fieldTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,fieldMemory⟩ :=
    testingFields_trace_memory program input read base n k readValues endpoint.error endpoint.charge
      (previous.getD tools abandonEntry) (P.menuBadBranch fee penalty previous tools).2 level
      (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0) readHeader readBase
      he hc hgo' hgr' hgf' hbo' hbr' hbf' hl' hb' fetchFields
  have firstJoin:=joinTrace_spec program input pointerTrace readTrace before pointed read 225 255
    pointerHead pointerLast readHead readLast pointerChain readChain pointerTime readTime
  have firstMemory:=joinTrace_memory pointerTrace readTrace before pointed base pointerLast pointerMemory readMemory
  have secondJoin:=joinTrace_spec program input (joinTrace pointerTrace readTrace) fieldTrace before read after 480 2640
    firstJoin.1 firstJoin.2.1 fieldHead fieldLast firstJoin.2.2.1 fieldChain firstJoin.2.2.2 fieldTime
  refine ⟨joinTrace (joinTrace pointerTrace readTrace) fieldTrace,after,secondJoin.1,secondJoin.2.1,
    secondJoin.2.2.1,secondJoin.2.2.2,afterHeader,?_,afterBase,?_,
    pointedFrame.trans (readFrame.trans afterFrame),afterOutput.trans readOutput,
    joinTrace_memory (joinTrace pointerTrace readTrace) fieldTrace before read base firstJoin.2.1 firstMemory fieldMemory⟩
  · calc
      _ = (List.range 6).map (fun offset =>
          testingFieldsValues readValues endpoint.error endpoint.charge (previous.getD tools abandonEntry)
            (P.menuBadBranch fee penalty previous tools).2 level
            (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0) (40+offset)) := by
        apply List.map_congr_left
        intro offset member
        exact afterHeader.value (40+offset) (by have inside:=List.mem_range.mp member; change 40+offset<48; omega)
      _ = _ := testingFieldsValues_original P readValues fee penalty previous tools level
  · rw [afterPC,readPC,selectedTestingCode,List.length_append,List.length_append,selectedPointerCode_length,scanEndpointCode_length]
    change before.pc+14+13+(headerCode testingFieldsCommands).length=
      before.pc+(14+13+(headerCode testingFieldsCommands).length)
    omega

end PDCompute.Solver
