module

public import Paid.PDCompute_Nat_SelectedPointerBits_018
public import Paid.PDCompute_SolverScanEndpointBits_174
public import Paid.PDCompute_SolverTestingBits_161
public import Paid.PDCompute_SolverSelectedRuntime_081

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 950000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- Original chosen cache-pair address, ACTUAL cache read, and real
six weighted testing fields, on ONE trace with every-prefix bits. -/
theorem selectedTesting_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools source level : ℕ)
    (before : State) (base n k budget S : ℕ) (values : ℕ → Cell)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hlevel : values 23=.natural level) (bound : level≤P.certificate.M)
    (hgo : values 10=.rational (previous.getD tools abandonEntry).observation)
    (hgr : values 11=.rational (previous.getD tools abandonEntry).repairs) (hgf : values 12=.rational (previous.getD tools abandonEntry).failure)
    (hbo : values 31=.rational (P.menuBadBranch fee penalty previous tools).2.observation)
    (hbr : values 32=.rational (P.menuBadBranch fee penalty previous tools).2.repairs) (hbf : values 33=.rational (P.menuBadBranch fee penalty previous tools).2.failure)
    (hb : values 34=.natural (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0))
    (safe : RootD27.Bits.SafeBits before budget)
    (goBits : ratEncodingBits (previous.getD tools abandonEntry).observation≤S)
    (grBits : ratEncodingBits (previous.getD tools abandonEntry).repairs≤S) (gfBits : ratEncodingBits (previous.getD tools abandonEntry).failure≤S)
    (boBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.observation≤S)
    (brBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.repairs≤S) (bfBits : ratEncodingBits (P.menuBadBranch fee penalty previous tools).2.failure≤S)
    (room : 1+64*(maximumMenuBits P fee+S+1)≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget)
    (counter : natBits (before.pc+(selectedTestingCode mode).length)≤budget) (fetch : FetchesCode program before.pc (selectedTestingCode mode)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤3120 ∧
      Header after base (selectedTestingValues P values fee penalty previous tools source level) ∧
      (List.range 6).map (fun offset=>after.heap (base+(40+offset)))=denseEncodeEntry (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level) ∧
      after.register .fresh=.natural base ∧ after.pc=before.pc+(selectedTestingCode mode).length ∧ Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let pointed:=selectedPointerResult before base source level
  let pointerValues:=Function.update values 39 (.natural (source+(1+2*level)))
  let endpoint:=P.cachedEndpoint P.endpointCache level
  let readValues:=scanEndpointValues pointerValues endpoint.error endpoint.charge
  have small : 4≤budget := by omega
  have codeLength : (selectedTestingCode mode).length=157 := rfl
  have globalCounter : natBits (before.pc+157)≤budget := by simpa only [codeLength] using counter
  obtain ⟨pointerTrace,pointerHead,pointerLast,pointerChain,pointerTime,pointedHeader,pointedFrame,pointerResources⟩:=
    PDCompute.NatControl.selectedPointer_trace_resources program input before base source level n k budget values header fresh hsourceValue hlevel safe addressBits
      ((Nat.add_le_add_left (natBits_mono (by omega : source+(1+2*level)≤source+(1+2*(P.certificate.M+1)))) 1).trans sourceBits)
      ((natBits_mono (by omega : before.pc+14≤before.pc+157)).trans globalCounter) fetch.append_left.append_left
  have pointerMemory : ∀ state∈pointerTrace,HeaderMemory before state base := fun state member=>(pointerResources state member).1
  have pointerSafe : ∀ state∈pointerTrace,RootD27.Bits.SafeBits state budget := fun state member=>(pointerResources state member).2
  have pointedBase : pointed.register .fresh=.natural base := fresh
  have pointedSource:=EndpointSource.frame_of_avoids mode input P source base n k before pointed hsource avoids pointedFrame
  have endpointCounter : natBits (pointed.pc+13)≤budget :=
    (natBits_mono (by change before.pc+14+13≤before.pc+157; omega)).trans globalCounter
  obtain ⟨readTrace,read,readHead,readLast,readChain,readTime,readHeader,readBase,readPC,readFrame,readOutput,readMemory,readSafe⟩:=
    scanEndpointCode_trace_bits mode program input P fee pointed base source level n k budget pointerValues pointedHeader pointedBase pointedSource bound rfl
      (pointerSafe pointed (List.mem_of_getLast? pointerLast)) small (by omega) addressBits
      ((Nat.add_le_add_left (natBits_mono (by omega : source+(1+2*level)+1≤source+(1+2*(P.certificate.M+1)))) 1).trans sourceBits)
      endpointCounter fetch.append_left.append_right
  have fetchFields : FetchesCode program read.pc (headerCode testingFieldsCommands) := by rw [readPC]; exact fetch.append_right
  have fieldCounter : natBits (read.pc+130)≤budget := by
    rw [readPC]
    simpa only [pointed,selectedPointerResult,Nat.add_assoc] using globalCounter
  have endpointBits:=originalEndpoint_cellBits P fee level bound
  have errorBound : ratEncodingBits endpoint.error≤maximumMenuBits P fee := by
    have actual : 1+ratEncodingBits endpoint.error≤1+maximumMenuBits P fee := endpointBits.1
    omega
  have chargeBound : ratEncodingBits endpoint.charge≤maximumMenuBits P fee := by
    have actual : 1+ratEncodingBits endpoint.charge≤1+maximumMenuBits P fee := endpointBits.2
    omega
  obtain ⟨fieldTrace,after,fieldHead,fieldLast,fieldChain,fieldTime,afterHeader,afterBase,afterPC,afterFrame,afterOutput,fieldResources⟩:=
    testingFields_trace_bits program input read base n k budget (maximumMenuBits P fee) S readValues endpoint.error endpoint.charge (previous.getD tools abandonEntry)
      (P.menuBadBranch fee penalty previous tools).2 level (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0)
      readHeader readBase (readSafe read (List.mem_of_getLast? readLast)) rfl rfl hgo hgr hgf hbo hbr hbf hlevel hb
      errorBound chargeBound goBits grBits gfBits boBits brBits bfBits room addressBits fieldCounter fetchFields
  have fieldMemory : ∀ state∈fieldTrace,HeaderMemory read state base := fun state member=>(fieldResources state member).1
  have fieldSafe : ∀ state∈fieldTrace,RootD27.Bits.SafeBits state budget := fun state member=>(fieldResources state member).2
  have firstJoin:=joinTrace_spec program input pointerTrace readTrace before pointed read 225 255 pointerHead pointerLast readHead readLast pointerChain readChain pointerTime readTime
  have firstMemory:=joinTrace_memory pointerTrace readTrace before pointed base pointerLast pointerMemory readMemory
  have secondJoin:=joinTrace_spec program input (joinTrace pointerTrace readTrace) fieldTrace before read after 480 2640
    firstJoin.1 firstJoin.2.1 fieldHead fieldLast firstJoin.2.2.1 fieldChain firstJoin.2.2.2 fieldTime
  refine ⟨joinTrace (joinTrace pointerTrace readTrace) fieldTrace,after,secondJoin.1,secondJoin.2.1,secondJoin.2.2.1,secondJoin.2.2.2,afterHeader,?_,afterBase,?_,
    pointedFrame.trans (readFrame.trans afterFrame),afterOutput.trans readOutput,
    joinTrace_memory (joinTrace pointerTrace readTrace) fieldTrace before read base firstJoin.2.1 firstMemory fieldMemory,
    PDCompute.Pack.joinTrace_invariant (joinTrace pointerTrace readTrace) fieldTrace (fun state=>RootD27.Bits.SafeBits state budget)
      (PDCompute.Pack.joinTrace_invariant pointerTrace readTrace (fun state=>RootD27.Bits.SafeBits state budget) pointerSafe readSafe) fieldSafe⟩
  · calc
      _ = (List.range 6).map (fun offset=>testingFieldsValues readValues endpoint.error endpoint.charge (previous.getD tools abandonEntry)
          (P.menuBadBranch fee penalty previous tools).2 level (if (P.menuBadBranch fee penalty previous tools).1=.repair then 1 else 0) (40+offset)) := by
        apply List.map_congr_left
        intro offset member
        exact afterHeader.value (40+offset) (by have inside:=List.mem_range.mp member; unfold headerWords; omega)
      _ = denseEncodeEntry (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level) :=
        testingFieldsValues_original P readValues fee penalty previous tools level
  · rw [afterPC,readPC,codeLength]
    change before.pc+14+13+130=before.pc+157
    omega

end PDCompute.Solver
