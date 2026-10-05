from typing import Any

from checker import check_invariant
from formula import And, Atom, Not, no_deadlock
from model import TransitionSystem, compose, handshake, interleave, parallel, phil, stick, stick_fixed


def process(i: int) -> TransitionSystem[str, str, str]:
  """Example 2.28: P_i alternates between noncrit_i and crit_i"""
  states = {f"noncrit{i}", f"crit{i}"}
  return TransitionSystem(
      states=states,
      actions={"request", "release"},
      transitions={(f"noncrit{i}", "request", f"crit{i}"), (f"crit{i}", "release", f"noncrit{i}")},
      initial={f"noncrit{i}"},
      ap=states,
      label={s: {s} for s in states},
  )


def arbiter() -> TransitionSystem[str, str, str]:
  states = {"unlock", "lock"}
  return TransitionSystem(
      states=states,
      actions={"request", "release"},
      transitions={("unlock", "request", "lock"), ("lock", "release", "unlock")},
      initial={"unlock"},
      ap=states,
      label={s: {s} for s in states},
  )


def test_arbiter_fig_2_12() -> None:
  # TS_Arb = (TS1 ||| TS2) || Arbiter
  ts_arb = parallel(interleave(process(1), process(2)), arbiter())
  assert ts_arb.reach() == {
      (("noncrit1", "noncrit2"), "unlock"),
      (("crit1", "noncrit2"), "lock"),
      (("noncrit1", "crit2"), "lock"),
  }


def test_interleave_fig_2_12_top() -> None:
  assert len(interleave(process(1), process(2)).reach()) == 4


def test_remark_2_27_empty_h_is_interleaving() -> None:
  a, b = interleave(process(1), process(2)), handshake(process(1), process(2), set())
  assert (a.states, a.transitions, a.initial, a.label) == (b.states, b.transitions, b.initial, b.label)


def test_parallel_would_wrongly_sync_p1_p2() -> None:
  # P1 || P2 handshakes on request: both enter crit together
  assert (("noncrit1", "noncrit2"), "request", ("crit1", "crit2")) in parallel(process(1), process(2)).transitions


def test_compose_is_left_fold_of_parallel() -> None:
  p0, s0, p1, s1 = phil(0, 2), stick(0, 2), phil(1, 2), stick(1, 2)
  nested = parallel(parallel(parallel(p0, s0), p1), s1)
  composed = compose([p0, s0, p1, s1])
  assert (composed.states, composed.transitions, composed.initial, composed.label) == (
      nested.states, nested.transitions, nested.initial, nested.label
  )


def deadlock_free(ts: TransitionSystem[Any, str, str], n: int) -> bool:
  return check_invariant(ts, no_deadlock([f"wait_{i}" for i in range(n)])) is None


def test_dining_philosophers_deadlock() -> None:
  for n in (2, 3):
    naive = compose([c for i in range(n) for c in (phil(i, n), stick(i, n))])
    fixed = compose([c for i in range(n) for c in (phil(i, n), stick_fixed(i, n))])
    assert not deadlock_free(naive, n)
    assert deadlock_free(fixed, n)


def test_invariant_counterexample_ends_in_bad_state() -> None:
  # vending machine (Example 2.2): "always ¬paid" fails, counterexample pay -> select
  states = {"pay", "select", "soda", "beer"}
  vm = TransitionSystem(
      states=states,
      actions={"insert_coin", "get_soda", "get_beer", "tau"},
      transitions={
          ("pay", "insert_coin", "select"),
          ("select", "tau", "soda"),
          ("select", "tau", "beer"),
          ("soda", "get_soda", "pay"),
          ("beer", "get_beer", "pay"),
      },
      initial={"pay"},
      ap={"paid", "drink"},
      label={"pay": set(), "soda": {"paid", "drink"}, "beer": {"paid", "drink"}, "select": {"paid"}},
  )
  cex = check_invariant(vm, Not(Atom("paid")))
  assert cex is not None and cex[0] == "pay" and "paid" in vm.label[cex[-1]]
  assert check_invariant(vm, Not(And(Atom("drink"), Not(Atom("paid"))))) is None
