import Mathlib.Logic.Basic
import Fixture.Command

/-! Declarations the library makes in a foreign namespace, Mathlib's `Nat`,
including an inductive with a `deriving` clause, an unnamed instance, a
`@[simp]` lemma proved by `rfl`, and a declaration a library-defined
command generates. -/

namespace Nat

/-- Doubling, declared in `Nat` so that `n.fixtureDouble` reads well. -/
def fixtureDouble (n : Nat) : Nat := n + n

@[simp] theorem fixtureDouble_zero : fixtureDouble 0 = 0 := rfl

/-- Two colors, with a derived instance. -/
inductive FixtureColor
  | red
  | blue
  deriving DecidableEq

instance : Inhabited FixtureColor := ⟨.red⟩

mk_const fixtureSeven 7

end Nat
