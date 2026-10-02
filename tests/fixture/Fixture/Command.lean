import Lean

/-! A library-defined command that elaborates a declaration it builds, the
pattern `lax-export` must expand, since the generated names cannot be
patched inside the invocation. -/

open Lean Elab Command

namespace Fixture

syntax (name := mkConst) "mk_const " ident num : command

@[command_elab mkConst]
def elabMkConst : CommandElab := fun stx => do
  let n : Ident := ⟨stx[1]⟩
  let k : TSyntax `num := ⟨stx[2]⟩
  elabCommand (← `(/-- A constant made by `mk_const`. -/ def $n : Nat := $k))

end Fixture
