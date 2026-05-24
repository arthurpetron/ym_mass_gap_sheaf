"""Generic runner for any `InductiveBoundWitness` instance.

The transferred lemma of `notes/codynamic-transfer.md` §7 in code:

    Given an initial state with positive ``remaining_budget`` and a
    constructive ``step()`` map, iterate K times accumulating
    per-step ``degradation``; the global glued-bound survives iff
    every step closes AND the total degradation stays under the
    initial budget.

This runner is identical for EKF and YM instances — that is the
load-bearing point of the codynamic-transfer template.
"""

from __future__ import annotations

from computations.transfer_examples.protocol import (
    InductiveBoundWitness,
    RunResult,
)


def run_inductive_steps(
    initial: InductiveBoundWitness, K: int
) -> RunResult:
    """Iterate the inductive bound-witness step ``K`` times.

    Stops early (with ``n_steps_taken < K``) if any ``step()`` returns
    ``None``, signaling local-update failure.  Always returns a
    ``RunResult``; check ``.closes`` for the final closure flag.

    The ``closes`` predicate is the constructive form of:

        every step succeeded  AND  Σ_k d_k < B_0.

    This is the §6/§7 type-signature obligation, common to EKF and YM.
    """
    if K < 0:
        raise ValueError(f"K must be non-negative; got {K}")

    initial_budget = initial.remaining_budget
    state: InductiveBoundWitness | None = initial
    n_steps_taken = 0
    total_degradation = 0.0
    per_step_bounds = [initial.bound_witness.bound]

    for _ in range(K):
        assert state is not None  # invariant; only updated below
        next_state = state.step()
        if next_state is None:
            # Local update failed; stop honestly with the partial run.
            return RunResult(
                final_state=state,
                n_steps_taken=n_steps_taken,
                total_degradation=total_degradation,
                initial_budget=initial_budget,
                final_budget=state.remaining_budget,
                closes=False,
                per_step_bounds=per_step_bounds,
            )
        total_degradation += state.degradation
        per_step_bounds.append(next_state.bound_witness.bound)
        state = next_state
        n_steps_taken += 1

    closes = (
        state is not None
        and total_degradation < initial_budget
        and state.bound_witness.bound > 0
    )
    return RunResult(
        final_state=state,
        n_steps_taken=n_steps_taken,
        total_degradation=total_degradation,
        initial_budget=initial_budget,
        final_budget=state.remaining_budget if state is not None else 0.0,
        closes=closes,
        per_step_bounds=per_step_bounds,
    )
