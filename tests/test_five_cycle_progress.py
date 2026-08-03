from __future__ import annotations

from copy import deepcopy
from pathlib import Path

import pytest

from scripts.five_cycle_progress import (
    apply_overrides,
    apply_parameter_overrides,
    load_state,
    render_chart,
)

STATE_PATH = Path(__file__).resolve().parents[1] / "docs" / "five-cycle-progress.json"


def test_default_chart_tracks_current_milestone() -> None:
    chart = render_chart(load_state(STATE_PATH))
    assert "progress: 8/8 stages complete" in chart
    assert "based cycles [0,4,5,6,10]" in chart
    assert "cycle space 2^7 = 128 closed surfaces" in chart
    assert "[x] determine exact centered-vacuum balance (complete)" in chart


def test_stage_overrides_are_validated_and_rendered() -> None:
    state = deepcopy(load_state(STATE_PATH))
    apply_overrides(state, ["haar5_evaluation=complete", "haar5_comparison=active"])
    chart = render_chart(state)
    assert "progress: 7/8 stages complete" in chart
    assert "[x] evaluate the two exact Haar_5 values (complete)" in chart
    assert "[>] compare row and constant Haar_5 values (active)" in chart


def test_unknown_stage_is_rejected() -> None:
    state = deepcopy(load_state(STATE_PATH))
    with pytest.raises(ValueError, match="unknown stage"):
        apply_overrides(state, ["imaginary_stage=complete"])


def test_chart_parameters_accept_json_overrides() -> None:
    state = deepcopy(load_state(STATE_PATH))
    apply_parameter_overrides(
        state,
        ["raw_links=120", "based_cycles=[1,2,3,4,5]"],
    )
    chart = render_chart(state)
    assert "Haar_120 raw links" in chart
    assert "based cycles [1,2,3,4,5]" in chart


def test_unknown_parameter_is_rejected() -> None:
    state = deepcopy(load_state(STATE_PATH))
    with pytest.raises(ValueError, match="unknown parameter"):
        apply_parameter_overrides(state, ["imaginary_parameter=1"])
