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
    assert "progress: 12/12 stages complete" in chart
    assert "based cycles [0,4,5,6,10]" in chart
    assert "cycle space 2^7 = 128 closed surfaces" in chart
    assert "[x] determine exact centered-vacuum balance (complete)" in chart
    assert "128/128 surfaces embedded" in chart
    assert "slab-embedding=128/128-closed-complete" in chart
    assert "[x] prove closed-surface sum equals the actual Haar_5 moments (complete)" in chart
    assert "face-weight=exact-(2*w^3)^F-kernel-checked" in chart
    assert "actual-transport+Haar5-topological-amplitude-kernel-checked" in chart
    assert "exact 116 -> 32 active links" in chart
    assert "128/128 maximal forests + rooted paths checked" in chart
    assert "concrete chord-only forest-gauge evaluator" in chart
    assert "all 127 nonempty mask values staged + kernel-checked" in chart
    assert "128/128 orientation-aware Haar ledgers checked" in chart
    assert "source degree-five + Haar invariance + cyclic words checked" in chart
    assert "physical factor/product lift kernel-checked" in chart
    assert "word reducer: free+cyclic+128/128 face specialization kernel-checked" in chart
    assert "qpoly=128+2-surface-sums-kernel-checked" in chart
    assert (
        "six-face=literal-raw-words+five-chord-Haar-1/16-kernel-checked"
        in chart
    )
    assert "haar=9/9-exact-representatives-cover-128/128" in chart
    assert (
        "bivalence=128/128-edge-valence-0-or-2-kernel-checked;fused-step-exact"
        in chart
    )
    assert "geometry=128/128-maximal-forests+root-paths-kernel-checked" in chart
    assert "lean-values=128/128-staged-kernel-checked" in chart
    assert "padded-active-word-to-chord-Haar-endpoint+translated-semantics" in chart
    assert "WHOLE-PROJECT FORMAL ROADMAP: CURRENT LEAN -> COMPLETE YANG--MILLS PROOF" in chart
    assert "high-level milestones: 3/9 complete" in chart
    assert "[x] finite campaign: actual BF4 Haar_5 surface bridge" in chart
    assert "supporting exact evidence; not alone a Clay closure" in chart
    assert "[ ] CLAY / JAFFE--WITTEN TARGET" in chart
    assert "complete formal dependency roadmap, not a claim" in chart
    assert "guarded frontier bundles remain deliberately uninhabited" in chart


def test_stage_overrides_are_validated_and_rendered() -> None:
    state = deepcopy(load_state(STATE_PATH))
    apply_overrides(state, ["haar5_evaluation=complete", "haar5_comparison=active"])
    chart = render_chart(state)
    assert "progress: 11/12 stages complete" in chart
    assert "[x] evaluate the two exact Haar_5 values (complete)" in chart
    assert "[>] compare row and constant Haar_5 values (active)" in chart


def test_project_stage_override_updates_full_path() -> None:
    state = deepcopy(load_state(STATE_PATH))
    apply_overrides(state, ["haar5_surface_bridge=complete"])
    chart = render_chart(state)
    assert "high-level milestones: 3/9 complete" in chart
    assert "[x] finite campaign: actual BF4 Haar_5 surface bridge" in chart


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
