import Fixture.Basic

namespace Fixture

/-- The target: field notation on a foreign declaration, the coercion, the
`@[simp]` lemma proved by `rfl`, the `twice%` macro, the derived instance,
and the generated constant. -/
theorem main (b : Box) (n : Nat) (c : Nat.FixtureColor) :
    b n + (twice% 0) = n.fixtureDouble - n + b.val + (if c = c then 0 else Nat.fixtureSeven) := by
  simp [Nat.fixtureDouble]
  omega

theorem rooted : Rooted.value = 3 := rfl

end Fixture
