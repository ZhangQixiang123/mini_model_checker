from typing import Any, cast
from checker import check_invariant
from model import compose, TransitionSystem
from formula import Formula, conjunction, Not, Atom


def phil(i: int, n: int) -> TransitionSystem[str, str, str]:
  l, r = i, (i - 1) % n
  states = {"think", "wait_left", "wait_right", "eat", "ret_left", "ret_right"}
  # component-specific atoms so each philosopher has its own wait_i
  def atom(s: str) -> str:
    return f"wait_{i}" if s in ("wait_left", "wait_right") else f"{s}_{i}"
  return TransitionSystem(
      states=states,
      actions={f"req_{l},{i}", f"req_{r},{i}", f"rel_{l},{i}", f"rel_{r},{i}"},
      transitions={
          ("think", f"req_{r},{i}", "wait_left"),
          ("think", f"req_{l},{i}", "wait_right"),
          ("wait_left", f"req_{l},{i}", "eat"),
          ("wait_right", f"req_{r},{i}", "eat"),
          ("eat", f"rel_{r},{i}", "ret_left"),
          ("ret_left", f"rel_{l},{i}", "think"),
          ("eat", f"rel_{l},{i}", "ret_right"),
          ("ret_right", f"rel_{r},{i}", "think"),
      },
      initial={"think"},
      ap={atom(s) for s in states},
      label={s: {atom(s)} for s in states},
  )
  
def stick(i: int, n: int) -> TransitionSystem[str, str, str]:
  j = (i + 1) % n
  states = {"avail", "occ_left", "occ_right"}
  return TransitionSystem(
      states=states,
      actions={f"req_{i},{i}", f"rel_{i},{i}", f"req_{i},{j}", f"rel_{i},{j}"},
      transitions={
          ("avail", f"req_{i},{i}", "occ_left"),
          ("occ_left", f"rel_{i},{i}", "avail"),
          ("avail", f"req_{i},{j}", "occ_right"),
          ("occ_right", f"rel_{i},{j}", "avail"),
      },
      initial={"avail"},
      ap=states,
      label={s: {s} for s in states},
  )


def stick_fixed(i: int, n: int) -> TransitionSystem[str, str, str]:
  """Fig 3.3: the stick alternates between philosopher i and philosopher i+1"""
  j = (i + 1) % n
  states = {"avail_mine", "occ_left", "avail_next", "occ_right"}
  return TransitionSystem(
      states=states,
      actions={f"req_{i},{i}", f"rel_{i},{i}", f"req_{i},{j}", f"rel_{i},{j}"},
      transitions={
          ("avail_mine", f"req_{i},{i}", "occ_left"),
          ("occ_left", f"rel_{i},{i}", "avail_next"),
          ("avail_next", f"req_{i},{j}", "occ_right"),
          ("occ_right", f"rel_{i},{j}", "avail_mine"),
      },
      initial={"avail_mine"} if i % 2 == 0 else {"avail_next"},
      ap=states,
      label={s: {s} for s in states},
  )

def no_deadlock() -> Formula[str]:
  """Book p. 108, Example 3.2: deadlock freedom as the invariant

      Φ = ¬wait_0 ∨ ¬wait_1 ∨ ... = ¬(wait_0 ∧ wait_1 ∧ ...)

  i.e. "not all philosophers are waiting for a chopstick".
  """
  return Not(conjunction([Atom(f"wait_{i}") for i in range(5)]))


def flatten(state: Any) -> list[Any]:
  """Decode a left-nested compose() state into its component states, leaf order first."""
  parts: list[Any] = []
  while isinstance(state, tuple):
    pair = cast(tuple[Any, Any], state)
    parts.append(pair[1])
    state = pair[0]
  parts.append(state)
  parts.reverse()
  return parts


def prettyprint(cex: list[Any], n: int) -> None:
  """Print a counterexample as one aligned row of the 2n component states per step."""
  labels = [f"{kind}{i}" for i in reversed(range(n)) for kind in ("phil", "stick")]
  order = [2 * i + k for i in reversed(range(n)) for k in (0, 1)]
  rows = [[flatten(s)[j] for j in order] for s in cex]
  widths = [len(lab) for lab in labels]
  for row in rows:
    for k, part in enumerate(row):
      widths[k] = max(widths[k], len(str(part)))
  print("    " + " ".join(lab.rjust(widths[k]) for k, lab in enumerate(labels)))
  for step, row in enumerate(rows):
    print(f"{step:>3} " + " ".join(str(part).rjust(widths[k]) for k, part in enumerate(row)))


def ts_wrong() -> TransitionSystem[Any, str, str]:
  phils = [phil(i, 5) for i in range(5)]
  sticks = [stick(i, 5) for i in range(5)]
  ls: list[TransitionSystem[str, str, str]] = []
  for i in range(5):
    ls.append(phils[i])
    ls.append(sticks[i])
  return compose(ls)

def ts_correct() -> TransitionSystem[Any, str, str]:
  phils = [phil(i, 5) for i in range(5)]
  sticks = [stick_fixed(i, 5) for i in range(5)]
  ls: list[TransitionSystem[str, str, str]] = []
  for i in range(5):
    ls.append(phils[i])
    ls.append(sticks[i])
  return compose(ls)

def evaluate[S, Act, AP](ts: TransitionSystem[S, Act, AP], formula: Formula[AP]) -> None:
  result = check_invariant(ts, formula)
  if result is None:
    print("True")
  else:
    prettyprint(result, 5)
    
evaluate(ts_wrong(), no_deadlock())
evaluate(ts_correct(), no_deadlock())