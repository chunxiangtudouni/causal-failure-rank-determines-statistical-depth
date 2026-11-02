module

import PaperProofs.Structure.CompactControllerA19Closure

set_option autoImplicit false
set_option warningAsError true

open PaperProofs.Structure.LaminarTree

universe u

example : CompactControllerClaims.FullClaims.{u} :=
  CompactControllerA19Closure.fullClaims
example : RawTreePreprocessingClaims.FullClaims :=
  CompactControllerA19Closure.fullClaims.{0}.1
example : AlgorithmClaims.FullGivenTreeClaims :=
  CompactControllerA19Closure.fullClaims.{0}.2.1
example : CompactControllerClaims.CallbackClaims :=
  CompactControllerA19Closure.fullClaims.{0}.2.2.1
example : CompactControllerClaims.MachineControllerClaims :=
  CompactControllerA19Closure.fullClaims.{0}.2.2.2.1
example : CompactControllerClaims.NativeCallbackClaims.{u} :=
  CompactControllerA19Closure.fullClaims.{u}.2.2.2.2
example : CompactControllerClaims.MachineControllerClaims :=
  CompactControllerA19Closure.machineControllerClaims

#print axioms CompactControllerA19Closure.fullClaims
#print axioms CompactControllerA19Closure.machineControllerClaims
