from typing import Any


class TransitionSystem[S, Act, AP]:
  def __init__(self, states: set[S], actions: set[Act], transitions: set[tuple[S, Act, S]],
              initial: set[S], ap: set[AP], label: dict[S, set[AP]]):
    self.states = states
    self.actions = actions 
    self.transitions = transitions 
    self.initial = initial 
    self.ap = ap 
    self.label = label 
    self._post: dict[S, set[S]] = {}
    for (u, _, t) in transitions:
      self._post.setdefault(u, set()).add(t)

  def post(self, s: S) -> set[S]:
    """Def 2.3: Post(s) = { s' | s --a--> s' for some a }"""
    return set(self._post.get(s, ()))

  def reach(self) -> set[S]:
    """Def 2.10: Reach(TS), all states reachable from some initial state"""
    visited: set[S] = set()
    stack = list(self.initial)
    while stack:
      s = stack.pop()
      if s in visited:
        continue
      visited.add(s)
      stack.extend(self.post(s))
    return visited
  
def handshake[S1, S2, Act, AP](
    ts1: TransitionSystem[S1, Act, AP],
    ts2: TransitionSystem[S2, Act, AP],
    h: set[Act]
) -> TransitionSystem[tuple[S1, S2], Act, AP]:
  """Def 2.26: TS1 ||_H TS2, with H ⊆ Act1 ∩ Act2 and τ ∉ H. Rules of Fig 2.11."""
  if not h <= ts1.actions & ts2.actions:
    raise ValueError(f"H must be a subset of Act1 ∩ Act2, extra: {h - (ts1.actions & ts2.actions)}")

  transitions: set[tuple[tuple[S1, S2], Act, tuple[S1, S2]]] = set()
  # interleaving for α ∉ H:  s1 --α-->_1 s1'  gives  <s1, s2> --α--> <s1', s2>  for every s2
  for (s1, a, t1) in ts1.transitions:
    if a not in h:
      for s2 in ts2.states:
        transitions.add(((s1, s2), a, (t1, s2)))
  # interleaving for α ∉ H:  s2 --α-->_2 s2'  gives  <s1, s2> --α--> <s1, s2'>  for every s1
  for (s2, a, t2) in ts2.transitions:
    if a not in h:
      for s1 in ts1.states:
        transitions.add(((s1, s2), a, (s1, t2)))
  # handshaking for α ∈ H:  s1 --α-->_1 s1' ∧ s2 --α-->_2 s2'  gives  <s1, s2> --α--> <s1', s2'>
  for (s1, a, t1) in ts1.transitions:
    if a in h:
      for (s2, b, t2) in ts2.transitions:
        if b == a:
          transitions.add(((s1, s2), a, (t1, t2)))

  return TransitionSystem(
      states={(s1, s2) for s1 in ts1.states for s2 in ts2.states},
      actions=ts1.actions | ts2.actions,
      transitions=transitions,
      initial={(i1, i2) for i1 in ts1.initial for i2 in ts2.initial},
      ap=ts1.ap | ts2.ap,
      label={(s1, s2): ts1.label[s1] | ts2.label[s2] for s1 in ts1.states for s2 in ts2.states},
  )


def interleave[S1, S2, Act, AP](
    ts1: TransitionSystem[S1, Act, AP], ts2: TransitionSystem[S2, Act, AP]
) -> TransitionSystem[tuple[S1, S2], Act, AP]:
  """Def 2.18: TS1 ||| TS2 = (S1 × S2, Act1 ∪ Act2, →, I1 × I2, AP1 ∪ AP2, L)"""
  transitions: set[tuple[tuple[S1, S2], Act, tuple[S1, S2]]] = set()
  # s1 --α-->_1 s1'  gives  <s1, s2> --α--> <s1', s2>
  for (s1, a, t1) in ts1.transitions:
    for s2 in ts2.states:
      transitions.add(((s1, s2), a, (t1, s2)))
  # s2 --α-->_2 s2'  gives  <s1, s2> --α--> <s1, s2'>
  for (s2, a, t2) in ts2.transitions:
    for s1 in ts1.states:
      transitions.add(((s1, s2), a, (s1, t2)))

  return TransitionSystem(
      states={(s1, s2) for s1 in ts1.states for s2 in ts2.states},
      actions=ts1.actions | ts2.actions,
      transitions=transitions,
      initial={(i1, i2) for i1 in ts1.initial for i2 in ts2.initial},
      ap=ts1.ap | ts2.ap,
      # L(<s1, s2>) = L1(s1) ∪ L2(s2)
      label={(s1, s2): ts1.label[s1] | ts2.label[s2] for s1 in ts1.states for s2 in ts2.states},
  )


def parallel[S1, S2, Act, AP](
    ts1: TransitionSystem[S1, Act, AP],
    ts2: TransitionSystem[S2, Act, AP]
) -> TransitionSystem[tuple[S1, S2], Act, AP]:
  """Notation after Def 2.26: TS1 || TS2 = TS1 ||_H TS2 with H = Act1 ∩ Act2, requiring τ ∉ H"""
  return handshake(ts1, ts2, ts1.actions & ts2.actions)


def compose[S, Act, AP](
    tss: list[TransitionSystem[S, Act, AP]]
) -> TransitionSystem[Any, Act, AP]:
  """TS_1 || ... || TS_n, the iterated binary parallel composition.

  Each step is the binary `parallel` (notation after Def 2.26), i.e. left || right
  with H = Act_left ∩ Act_right. The state space is the iterated Cartesian product,
  so states are left-nested tuples: ((s0, s1), s2), ... (book p. 49, n > 0).

  Book's assumptions: H_i,j ∩ Act_k = {} for k not in {i, j}, and tau not in H_i,j.
  """
  if not tss:
    raise ValueError("compose requires at least one transition system")
  result: TransitionSystem[Any, Act, AP] = tss[0]
  for ts in tss[1:]:
    result = parallel(result, ts)
  return result


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





