module

import RootA19_OriginalFull_001
public import PaperProofs.Structure.CompactControllerClaims

set_option autoImplicit false
set_option warningAsError true

namespace PaperProofs.Structure.LaminarTree.CompactControllerA19Closure

universe u

/-- The original complete A19 target, including A06/A17 and arbitrary Seed universes. -/
public theorem fullClaims : CompactControllerClaims.FullClaims.{u} :=
  RootA19.OriginalFull.fullClaims

/-- A fixed raw preprocessor and live packed controller, with all original resources. -/
public theorem machineControllerClaims : CompactControllerClaims.MachineControllerClaims :=
  fullClaims.{0}.2.2.2.1

end PaperProofs.Structure.LaminarTree.CompactControllerA19Closure
