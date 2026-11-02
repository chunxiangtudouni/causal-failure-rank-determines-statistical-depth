module

public import Paid.RootD27Endpoint_HeaderInit_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Endpoint

open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

theorem fetch_take {program : Program} {origin : ℕ} {code : List Instruction}
    (fetched : FetchesCode program origin code) (count : ℕ) : FetchesCode program origin (code.take count) := by
  intro offset inside
  have codeBound : offset<code.length := lt_of_lt_of_le inside (List.length_take_le' count code)
  have countBound : offset<count := lt_of_lt_of_le inside (List.length_take_le count code)
  exact (fetched offset codeBound).trans (List.getElem?_take_of_lt countBound).symm

theorem endpoint_located_fetch (origin : ℕ) :
    FetchesCode (locatedBlock origin (endpointProgram origin)) origin (endpointCode origin) := by
  intro offset _
  rw [locatedBlock_fetch]
  simp only [endpointProgram,List.getElem?_toArray]

theorem endpoint_layout_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program origin (initializationCode origin++
      (rowTestCode (origin+113) (origin+229)++(rowBodyCode (origin+105)++returnCode))) := by
  simpa only [endpointCode,List.append_assoc] using fetched

theorem endpoint_init_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program origin (initializationCode origin) := (endpoint_layout_fetch program origin fetched).append_left

theorem endpoint_init_layout_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program origin (solverPrologue++(paddingSetup++
      (baseRowCode (origin+19)++(headerCode initialCommands++cacheHeaderCode)))) := by
  simpa only [initializationCode,List.append_assoc] using endpoint_init_fetch program origin fetched

theorem endpoint_test_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program (origin+105) (rowTestCode (origin+113) (origin+229)) := by
  simpa only [initializationCode_length] using (endpoint_layout_fetch program origin fetched).append_right.append_left

theorem endpoint_body_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program (origin+113) (rowBodyCode (origin+105)) := by
  simpa only [initializationCode_length,rowTestCode_length,Nat.add_assoc] using
    (endpoint_layout_fetch program origin fetched).append_right.append_right.append_left

theorem endpoint_return_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program (origin+229) returnCode := by
  simpa only [initializationCode_length,rowTestCode_length,rowBodyCode_length,Nat.add_assoc] using
    (endpoint_layout_fetch program origin fetched).append_right.append_right.append_right

theorem endpoint_prologue_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program origin solverPrologue := (endpoint_init_layout_fetch program origin fetched).append_left

theorem endpoint_padding_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program (origin+19) (baseRowCode (origin+19)) := by
  simpa only [solverPrologue_length,paddingSetup_length,Nat.add_assoc] using
    (endpoint_init_layout_fetch program origin fetched).append_right.append_right.append_left

theorem endpoint_paddingLead_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program (origin+16) paddingLeadCode := by
  have follow:=(endpoint_init_layout_fetch program origin fetched).append_right
  have leadFetch:=fetch_take follow 4
  have literal : (paddingSetup++(baseRowCode (origin+19)++(headerCode initialCommands++cacheHeaderCode))).take 4=
      paddingLeadCode := rfl
  rw [literal] at leadFetch
  simpa only [solverPrologue_length] using leadFetch

theorem endpoint_scalar_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program (origin+37) (headerCode initialCommands) := by
  simpa only [solverPrologue_length,paddingSetup_length,baseRowCode_length,Nat.add_assoc] using
    (endpoint_init_layout_fetch program origin fetched).append_right.append_right.append_right.append_left

theorem endpoint_cacheHead_fetch (program : Program) (origin : ℕ)
    (fetched : FetchesCode program origin (endpointCode origin)) :
    FetchesCode program (origin+93) cacheHeaderCode := by
  simpa only [solverPrologue_length,paddingSetup_length,baseRowCode_length,initialScalar_length,Nat.add_assoc] using
    (endpoint_init_layout_fetch program origin fetched).append_right.append_right.append_right.append_right

end RootD27.Endpoint
