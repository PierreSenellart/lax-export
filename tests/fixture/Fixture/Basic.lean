import Fixture.Foreign
import Fixture.Syntax
import Fixture.Extra

namespace Fixture

/-- A box, applied to numbers through a coercion. -/
structure Box where
  val : Nat

/-- Structure-instance syntax on the shared structure: the field names must
stay bare once `Box` comes from the concepts. -/
def unit : Box := { val := 1 }

/-- The same with a binder-carrying field, as a function. -/
def shifted (k : Nat) : Box where
  val := k + 1

/-- A generated constant of the shared structure, used by name. -/
theorem unit_eq : unit = shifted 0 := by
  simp only [unit, shifted, Box.mk.injEq]

/-- The coercion: an instance the proof terms never mention. -/
instance : CoeFun Box (fun _ => Nat → Nat) := ⟨fun b n => b.val + n⟩

/-- Proved by `rfl`, used by `simp` as a definitional rewrite. -/
@[simp] theorem box_apply (b : Box) (n : Nat) : b n = b.val + n := rfl

private def secret (n : Nat) : Nat := n

theorem secret_eq (n : Nat) : secret n = n := rfl

/-- Mentions the private name through `secret_eq`, from the same module. -/
theorem uses_secret (n : Nat) : secret_eq n = secret_eq n := rfl

/-- Declared through `_root_`. -/
def _root_.Fixture.Rooted.value : Nat := 3

/-- Not reached by any target: must be dropped. -/
theorem unused_lemma : True := trivial

end Fixture
