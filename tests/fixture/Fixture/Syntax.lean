import Mathlib.Logic.Basic

/-! A notation module: nothing here reaches a proof term, yet a module using
`twice%` cannot parse without it. -/

namespace Fixture

/-- `twice% t` is `t + t`. -/
syntax "twice% " term : term

macro_rules
  | `(twice% $t) => `($t + $t)

/-- A syntax category: its constant lives under `Lean.Parser.Category`, so a
use of it must be expanded away and its parsers dropped. -/
declare_syntax_cat fixnum

syntax num : fixnum
syntax "double " fixnum : fixnum
syntax "fix% " fixnum : term

macro_rules
  | `(fix% $n:num) => `(($n : Nat))
  | `(fix% double $x:fixnum) => `(fix% $x + fix% $x)

end Fixture
