module

public import Paid.PDCompute_SolverEndpointPairBits_170
public import Paid.PDCompute_SolverEndpointMemory_065
public import Paid.PDCompute_Pack_SlotBitTrace_064

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (storeSlot storeSlotResult)

/-- Real pair read followed by real Header26/27 stores. Both data words
are read BEFORE either store; SAME trace carries every-prefix memory/bits. -/
theorem endpointHeader_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell) (before : State)
    (base address budget : ℕ) (values : ℕ → Cell) (error charge : ℚ)
    (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (haddress : before.register .address=.natural address)
    (herror : mode.HasCell input before address (.rational error)) (hcharge : mode.HasCell input before (address+1) (.rational charge))
    (safe : RootD27.Bits.SafeBits before budget) (small : 4≤budget)
    (errorBits : (.rational error : Cell).bits≤budget) (chargeBits : (.rational charge : Cell).bits≤budget)
    (pointerBits : 1+natBits (address+1)≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (counter : natBits (before.pc+10)≤budget) (fetch : FetchesCode program before.pc (endpointHeaderCode mode)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (endpointHeaderResult before base address error charge) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤195 ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let paired:=endpointPairResult before address error charge
  let first:=storeSlotResult paired base 26 .total
  let after:=endpointHeaderResult before base address error charge
  obtain ⟨pairTrace,pairHead,pairLast,pairChain,pairTime,pairResources⟩:=endpointPair_trace_bits mode program input before base address budget error charge haddress herror hcharge
    safe small errorBits chargeBits pointerBits ((natBits_mono (by omega : before.pc+4≤before.pc+10)).trans counter) fetch.append_left.append_left
  have pairMemory : ∀ state∈pairTrace,HeaderMemory before state base := fun state member=>(pairResources state member).1
  have pairSafe : ∀ state∈pairTrace,RootD27.Bits.SafeBits state budget := fun state member=>(pairResources state member).2
  have pairedSafe:=pairSafe paired (List.mem_of_getLast? pairLast)
  have pairedHeader : Header paired base values := header
  have pairedBase : paired.register .fresh=.natural base := by simp [paired,endpointPairResult,fresh]
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have firstCounter : natBits (paired.pc+3)≤budget :=
    (natBits_mono (by change before.pc+4+3≤before.pc+10; omega)).trans counter
  have firstFetch : FetchesCode program paired.pc (storeSlot 26 .total) := fetch.middle
  obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory,firstSafe⟩:=PDCompute.Pack.storeSlot_trace_safe program input paired base 26 budget .total values
    pairedHeader (by decide) pairedBase (by decide) pairedSafe (slotBits 26 (by decide)) firstCounter firstFetch
  have firstHeader : Header first base (Function.update values 26 (.rational error)) := by
    apply Header.update pairedHeader 26 (.rational error)
    · simp [first,storeSlotResult,paired,endpointPairResult]
    · exact Finset.subset_insert _ _
  have firstBase : first.register .fresh=.natural base := pairedBase
  have firstBound:=firstSafe first (List.mem_of_getLast? firstLast)
  have lastCounter : natBits (first.pc+3)≤budget := by simpa only [first,storeSlotResult,paired,endpointPairResult,Nat.add_assoc] using counter
  have lastFetch : FetchesCode program first.pc (storeSlot 27 .value) := fetch.append_right
  obtain ⟨lastTrace,lastHead,lastLast,lastChain,lastTime,lastMemory,lastSafe⟩:=PDCompute.Pack.storeSlot_trace_safe program input first base 27 budget .value
    (Function.update values 26 (.rational error)) firstHeader (by decide) firstBase (by decide) firstBound (slotBits 27 (by decide)) lastCounter lastFetch
  have firstJoin:=joinTrace_spec program input pairTrace firstTrace before paired first 75 60 pairHead pairLast firstHead firstLast pairChain firstChain pairTime firstTime
  have joined:=joinTrace_spec program input (joinTrace pairTrace firstTrace) lastTrace before first after 135 60
    firstJoin.1 firstJoin.2.1 lastHead lastLast firstJoin.2.2.1 lastChain firstJoin.2.2.2 lastTime
  exact ⟨joinTrace (joinTrace pairTrace firstTrace) lastTrace,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    joinTrace_memory (joinTrace pairTrace firstTrace) lastTrace before first base firstJoin.2.1
      (joinTrace_memory pairTrace firstTrace before paired base pairLast pairMemory firstMemory) lastMemory,
    PDCompute.Pack.joinTrace_invariant (joinTrace pairTrace firstTrace) lastTrace (fun state=>RootD27.Bits.SafeBits state budget)
      (PDCompute.Pack.joinTrace_invariant pairTrace firstTrace (fun state=>RootD27.Bits.SafeBits state budget) pairSafe firstSafe) lastSafe⟩

end PDCompute.Solver
