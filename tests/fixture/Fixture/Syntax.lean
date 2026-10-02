import Mathlib.Logic.Basic

/-! A notation module: nothing here reaches a proof term, yet a module using
`twice%` cannot parse without it. -/

namespace Fixture

/-- `twice% t` is `t + t`. -/
syntax "twice% " term : term

macro_rules
  | `(twice% $t) => `($t + $t)

end Fixture
