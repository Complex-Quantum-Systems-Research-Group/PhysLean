import Lake
open System Lake DSL

package «quantumInfo»

require "mathlib" from git "https://github.com/leanprover-community/mathlib4.git" @ "8f9d9cff6bd728b17a24e163c9402775d9e6a365"

--require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_lib QuantumInfo

lean_lib ClassicalInfo

lean_lib StatMech
