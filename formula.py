from typing import override


# Propositional logic over AP (Appendix A.3): Φ ::= true | a | ¬Φ | Φ ∧ Φ
class Top:
  @override
  def __repr__(self) -> str:
    return "true"


class Atom[AP]:
  def __init__(self, a: AP) -> None:
    self.a = a

  @override
  def __repr__(self) -> str:
    return f"{self.a}"


class Not[AP]:
  def __init__(self, phi: "Formula[AP]") -> None:
    self.phi = phi

  @override
  def __repr__(self) -> str:
    return f"!{self.phi!r}"


class And[AP]:
  def __init__(self, left: "Formula[AP]", right: "Formula[AP]") -> None:
    self.left = left
    self.right = right

  @override
  def __repr__(self) -> str:
    return f"({self.left!r} & {self.right!r})"


type Formula[AP] = Top | Atom[AP] | Not[AP] | And[AP]


def Or[AP](left: Formula[AP], right: Formula[AP]) -> Formula[AP]:
  """Φ ∨ Ψ = ¬(¬Φ ∧ ¬Ψ)"""
  return Not(And(Not(left), Not(right)))


def conjunction[AP](phis: list[Formula[AP]]) -> Formula[AP]:
  """Φ_0 ∧ ... ∧ Φ_{n-1}; the empty conjunction is true."""
  if not phis:
    return Top()
  result = phis[0]
  for phi in phis[1:]:
    result = And(result, phi)
  return result


def no_deadlock[AP](waiting: list[AP]) -> Formula[AP]:
  """Book p. 108, Example 3.2: deadlock freedom as the invariant

      Φ = ¬wait_0 ∨ ¬wait_1 ∨ ... = ¬(wait_0 ∧ wait_1 ∧ ...)

  i.e. "not all philosophers are waiting for a chopstick".
  """
  return Not(conjunction([Atom(a) for a in waiting]))


def holds[AP](a: set[AP], phi: Formula[AP]) -> bool:
  """A ⊨ Φ for an evaluation A ⊆ AP; s ⊨ Φ iff L(s) ⊨ Φ (book p. 21)"""
  if isinstance(phi, Top):
    return True
  if isinstance(phi, Atom):
    return phi.a in a
  if isinstance(phi, Not):
    return not holds(a, phi.phi)
  return holds(a, phi.left) and holds(a, phi.right)