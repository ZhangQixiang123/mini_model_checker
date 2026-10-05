from model import TransitionSystem
from formula import Formula, holds, conjunction, Not, Atom


def check_invariant[S, Act, AP](ts: TransitionSystem[S, Act, AP], phi: Formula[AP]) -> list[S] | None:
  """Algorithm 4: TS ⊨ "always Φ"?

  Returns None for "yes", otherwise a counterexample s0 s1 ... sn with sn ⊭ Φ.
  """
  r: set[S] = set()  # the set of reachable states
  u: list[S] = []  # the stack
  b = True  # all states in R satisfy Φ

  def visit(s: S) -> None:
    nonlocal b
    u.append(s)
    r.add(s)
    while True:
      s1 = u[-1]
      if ts.post(s1) <= r:
        b = b and holds(ts.label[s1], phi)
        if b:
          u.pop()  # book pops before checking Φ, which loses the bad state from the counterexample
      else:
        s2 = next(iter(ts.post(s1) - r))
        u.append(s2)
        r.add(s2)
      if not u or not b:
        break
  while ts.initial - r and b:
    visit(next(iter(ts.initial - r)))
  return None if b else u


# def no_deadlock[AP](waiting: list[AP]) -> Formula[AP]:
#   """Book p. 108, Example 3.2: deadlock freedom as the invariant

#       Φ = ¬wait_0 ∨ ¬wait_1 ∨ ... = ¬(wait_0 ∧ wait_1 ∧ ...)

#   i.e. "not all philosophers are waiting for a chopstick".
#   """
#   return Not(conjunction([Atom(a) for a in waiting]))


