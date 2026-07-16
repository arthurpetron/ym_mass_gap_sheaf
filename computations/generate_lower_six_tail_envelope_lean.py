#!/usr/bin/env python3
"""Generate exact Lean coefficient tables for the E8/E9 tail envelopes.

The source polynomials and both projective charts come from
``lower_six_tail_second_flux_certificate.py``.  Every operation in this
generator is over ``int`` or ``Fraction``; no floating-point value is used.

For each of E8/E9 and chart A/B the emitted tables contain:

* the native nonnegative tensor-Bernstein coefficients;
* the scaled power coefficients of the transformed chart polynomial;
* the cached first (x-coordinate) Pascal pass;
* the pre-chart coefficients before the final shift/substitution.

The chart-A pre-table is shifted by ``t = 1+r``.  The chart-B pre-table is
substituted by ``r = z + x/182*(1-z)``.  These relations are recomputed and
asserted exactly before any Lean source is written.
"""

from __future__ import annotations

from fractions import Fraction
from math import comb, lcm
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parent))
import lower_six_tail_second_flux_certificate as source  # noqa: E402


ROW_SHARD_SIZE = 7
CLEAR_SCALE = {"E8": 28_576_800, "E9": 257_191_200}


def case_data(label: str, chart: str) -> dict[str, object]:
    assert label in {"E8", "E9"}
    assert chart in {"A", "B"}
    polynomial = source.E8_NUM if label == "E8" else source.E9_NUM
    transform = (
        source.chart_a_power_coefficients
        if chart == "A"
        else source.chart_b_power_coefficients
    )
    power, total_degree = transform(polynomial)
    degree_x = max(a for a, _ in power)
    degree_y = max(b for _, b in power)
    assert total_degree == 89

    bernstein = source.bernstein_coefficients(power, degree_x, degree_y)
    table_scale = lcm(*(value.denominator for value in bernstein.values()))
    clear_scale = CLEAR_SCALE[label]
    assert table_scale % clear_scale == 0
    chart_quotient = table_scale // clear_scale

    def zero_grid() -> list[list[int]]:
        return [
            [0 for _ in range(degree_y + 1)]
            for _ in range(degree_x + 1)
        ]

    scaled_power = zero_grid()
    for (a, b), coefficient in power.items():
        value = coefficient * table_scale
        assert value.denominator == 1
        scaled_power[a][b] = value.numerator

    bernstein_rows = zero_grid()
    for i in range(degree_x + 1):
        for j in range(degree_y + 1):
            value = bernstein[i, j] * table_scale
            assert value.denominator == 1
            assert value.numerator >= 0
            bernstein_rows[i][j] = value.numerator

    x_pascal = zero_grid()
    for i in range(degree_x + 1):
        for b in range(degree_y + 1):
            x_pascal[i][b] = sum(
                scaled_power[a][b] * comb(degree_x - a, i - a)
                for a in range(i + 1)
            )

    for i in range(degree_x + 1):
        for j in range(degree_y + 1):
            transformed = sum(
                x_pascal[i][b] * comb(degree_y - b, j - b)
                for b in range(j + 1)
            )
            weighted = (
                bernstein_rows[i][j]
                * comb(degree_x, i)
                * comb(degree_y, j)
            )
            assert transformed == weighted

    # Coefficients after D=r/s^2, n=1/s and x=constant*s, before
    # chart A's r=1+y shift or chart B's affine r substitution.
    constant = 64 if chart == "A" else 91
    pre_chart = zero_grid()
    for (i, j), coefficient_expr in polynomial.terms():
        coefficient = source.exact_fraction(coefficient_expr)
        x_degree = total_degree - 2 * i - j
        value = coefficient * Fraction(table_scale, constant**x_degree)
        assert value.denominator == 1
        pre_chart[x_degree][i] += value.numerator

    if chart == "A":
        for a in range(degree_x + 1):
            for b in range(degree_y + 1):
                expected = sum(
                    pre_chart[a][i] * comb(i, b)
                    for i in range(b, degree_y + 1)
                )
                assert expected == scaled_power[a][b]
    else:
        reconstructed: dict[tuple[int, int], Fraction] = {}
        for a in range(degree_x + 1):
            for i in range(degree_y + 1):
                coefficient = pre_chart[a][i]
                if coefficient == 0:
                    continue
                for ell in range(i + 1):
                    for q in range(ell + 1):
                        key = (a + ell, i - ell + q)
                        value = Fraction(
                            coefficient
                            * comb(i, ell)
                            * comb(ell, q)
                            * (-1) ** q,
                            182**ell,
                        )
                        reconstructed[key] = reconstructed.get(
                            key, Fraction(0)
                        ) + value
        for a in range(degree_x + 1):
            for b in range(degree_y + 1):
                value = reconstructed.get((a, b), Fraction(0))
                assert value.denominator == 1
                assert value.numerator == scaled_power[a][b]
        assert not any(
            value
            for (a, b), value in reconstructed.items()
            if a > degree_x or b > degree_y
        )

    return {
        "label": label,
        "chart": chart,
        "total_degree": total_degree,
        "degree_x": degree_x,
        "degree_y": degree_y,
        "table_scale": table_scale,
        "clear_scale": clear_scale,
        "chart_quotient": chart_quotient,
        "scaled_power": scaled_power,
        "x_pascal": x_pascal,
        "bernstein": bernstein_rows,
        "pre_chart": pre_chart,
    }


def case_stem(label: str, chart: str) -> str:
    return f"tailEnvelope{label}Chart{chart}"


def module_stem(label: str, chart: str) -> str:
    return f"HarmonicLowerSixTailEnvelopeCertificate{label}Chart{chart}Rows"


def render_shard(data: dict[str, object], shard: int) -> str:
    label = str(data["label"])
    chart = str(data["chart"])
    stem = case_stem(label, chart)
    start = shard * ROW_SHARD_SIZE
    stop = min(start + ROW_SHARD_SIZE, int(data["degree_x"]) + 1)
    assert start < stop
    lines = [
        "/-",
        f"# Exact lower-six {label} chart-{chart} coefficient rows {shard}",
        "",
        "Generated by",
        "`computations/generate_lower_six_tail_envelope_lean.py`.",
        "-/",
        "",
        "import YMGap.Continuum.TensorBernsteinSeparableReconstruction",
        "",
        "namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows",
        "",
    ]
    for suffix, key in [
        ("ScaledPower", "scaled_power"),
        ("XPascal", "x_pascal"),
        ("Bernstein", "bernstein"),
        ("PreChart", "pre_chart"),
    ]:
        rows = data[key]
        assert isinstance(rows, list)
        lines.append(
            f"def {stem}{suffix}Rows{shard} : List (List Int) := ["
        )
        for row in rows[start:stop]:
            lines.append("  [" + ", ".join(str(value) for value in row) + "],")
        lines.extend(["]", ""])
    lines.append(
        "end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows"
    )
    lines.append("")
    return "\n".join(lines)


def balanced_append(names: list[str], indent: str = "  ") -> str:
    assert names
    if len(names) == 1:
        return names[0]
    midpoint = len(names) // 2
    left = balanced_append(names[:midpoint], indent + "  ")
    right = balanced_append(names[midpoint:], indent + "  ")
    return f"({left}) ++\n{indent}({right})"


def render_umbrella(data: dict[str, object]) -> str:
    label = str(data["label"])
    chart = str(data["chart"])
    stem = case_stem(label, chart)
    module = module_stem(label, chart)
    shard_count = (int(data["degree_x"]) + ROW_SHARD_SIZE) // ROW_SHARD_SIZE
    lines = [
        "/-",
        f"# Exact lower-six {label} chart-{chart} coefficient table",
        "",
        "Generated by",
        "`computations/generate_lower_six_tail_envelope_lean.py`.",
        "-/",
        "",
    ]
    for shard in range(shard_count):
        lines.append(
            f"import YMGap.Continuum.{module}{shard}"
        )
    lines.extend([
        "",
        "namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows",
        "",
        f"def {stem}TotalDegree : Nat := {data['total_degree']}",
        f"def {stem}DegreeX : Nat := {data['degree_x']}",
        f"def {stem}DegreeY : Nat := {data['degree_y']}",
        f"def {stem}TableScale : Nat := {data['table_scale']}",
        f"def {stem}ClearScale : Nat := {data['clear_scale']}",
        f"def {stem}ChartQuotient : Nat := {data['chart_quotient']}",
        "",
    ])
    for suffix in ["ScaledPower", "XPascal", "Bernstein", "PreChart"]:
        names = [f"{stem}{suffix}Rows{shard}" for shard in range(shard_count)]
        expression = balanced_append(names).replace("\n", "\n  ")
        lines.extend([
            f"def {stem}{suffix}Rows : List (List Int) :=",
            "  " + expression,
            "",
        ])
    lines.append(
        "end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows"
    )
    lines.append("")
    return "\n".join(lines)


def render_certificate_slice(data: dict[str, object], shard: int) -> str:
    label = str(data["label"])
    chart = str(data["chart"])
    stem = case_stem(label, chart)
    module = module_stem(label, chart)
    degree_x = int(data["degree_x"])
    degree_y = int(data["degree_y"])
    start = shard * ROW_SHARD_SIZE
    height = min(ROW_SHARD_SIZE, degree_x + 1 - start)
    assert height > 0
    constant = 64 if chart == "A" else 91
    namespace = (
        "YMGap.Continuum."
        f"HarmonicLowerSixTailEnvelopeCertificate{label}Chart{chart}"
    )
    lines = [
        "/-",
        f"# Closed {label} chart-{chart} coefficient slice {shard}",
        "",
        "Generated by",
        "`computations/generate_lower_six_tail_envelope_lean.py`.",
        "-/",
        "",
        f"import YMGap.Continuum.{module}",
        "import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRawRows",
        "import YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel",
        "",
        f"namespace {namespace}",
        "",
        "set_option maxHeartbeats 100000000",
        "set_option maxRecDepth 1000000",
        "",
        "open YMGap.RG",
        "open YMGap.Continuum.TensorBernsteinSeparableReconstruction",
        "open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCoefficientKernel",
        "open YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows",
        "",
        f"theorem {stem}_xPascal_slice{shard} :",
        f"    GridRelationSlice {start} {height} {degree_y + 1}",
        f"      (gridCoeff {stem}XPascalRows{shard})",
        f"      (xPascalExpected {degree_x} {stem}ScaledPowerRows) = true := by",
        "  rfl",
        "",
        f"theorem {stem}_yPascal_slice{shard} :",
        f"    GridRelationSlice {start} {height} {degree_y + 1}",
        "      (fun localRow j =>",
        f"        gridCoeff {stem}BernsteinRows{shard} localRow j *",
        "          Int.ofNat",
        f"            (binom {degree_x} ({start} + localRow) *",
        f"              binom {degree_y} j))",
        f"      (yPascalExpected {degree_y} {stem}XPascalRows) = true := by",
        "  rfl",
        "",
        f"theorem {stem}_nonnegative_slice{shard} :",
        f"    GridNonnegative {height} {degree_y + 1}",
        f"      (gridCoeff {stem}BernsteinRows{shard}) = true := by",
        "  rfl",
        "",
    ]
    if chart == "A":
        lines.extend([
            f"theorem {stem}_shift_slice{shard} :",
            f"    GridRelationSlice {start} {height} {degree_y + 1}",
            f"      (gridCoeff {stem}ScaledPowerRows{shard})",
            "      (fun a b =>",
            f"        upperBinomialTransform {degree_y}",
            f"          (fun i => gridCoeff {stem}PreChartRows a i) b) = true := by",
            "  rfl",
            "",
        ])
    else:
        lines.extend([
            f"theorem {stem}_affine_slice{shard} :",
            f"    GridRelationSlice {start} {height} {degree_y + 1}",
            "      (fun localRow b =>",
            f"        gridCoeff {stem}ScaledPowerRows{shard} localRow b *",
            f"          Int.ofNat (182 ^ {degree_y}))",
            f"      (affineChartBClearedCoeff {degree_y} {stem}PreChartRows) = true := by",
            "  rfl",
            "",
        ])
    lines.extend([
        f"theorem {stem}_raw_slice{shard} :",
        f"    GridRelationSlice {start} {height} {degree_y + 1}",
        "      (fun localRow i =>",
        f"        gridCoeff {stem}PreChartRows{shard} localRow i *",
        f"          Int.ofNat ({constant} ^ ({start} + localRow)))",
        f"      (quadraticRawExpected 89 {stem}ChartQuotient",
        f"        tailEnvelope{label}ClearedRows) = true := by",
        "  rfl",
        "",
    ])
    gates = ["xPascal", "yPascal", "nonnegative"]
    gates.append("shift" if chart == "A" else "affine")
    gates.append("raw")
    for gate in gates:
        lines.append(f"#print axioms {stem}_{gate}_slice{shard}")
    lines.extend(["", f"end {namespace}", ""])
    return "\n".join(lines)


def raw_rows(label: str) -> list[list[int]]:
    polynomial = source.E8_NUM if label == "E8" else source.E9_NUM
    clear_scale = CLEAR_SCALE[label]
    degree_d = polynomial.degree(source.D)
    degree_n = polynomial.degree(source.n)
    rows = [[0 for _ in range(degree_n + 1)] for _ in range(degree_d + 1)]
    for (i, j), coefficient_expr in polynomial.terms():
        value = source.exact_fraction(coefficient_expr) * clear_scale
        assert value.denominator == 1
        rows[i][j] = value.numerator
    return rows


def render_raw_rows() -> str:
    lines = [
        "/-",
        "# Exact cleared E8/E9 raw coefficient rows",
        "",
        "Generated by",
        "`computations/generate_lower_six_tail_envelope_lean.py`.",
        "-/",
        "",
        "import YMGap.Continuum.TensorBernsteinSeparableReconstruction",
        "",
        "namespace YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows",
        "",
        "set_option maxHeartbeats 2000000",
        "",
    ]
    for label in ["E8", "E9"]:
        rows = raw_rows(label)
        lines.append(f"def tailEnvelope{label}ClearedRows : List (List Int) := [")
        for row in rows:
            lines.append("  [" + ", ".join(str(value) for value in row) + "],")
        lines.extend(["]", ""])
    lines.append(
        "end YMGap.Continuum.HarmonicLowerSixTailEnvelopeCertificateRows"
    )
    lines.append("")
    return "\n".join(lines)


def write_all(repo_root: Path) -> None:
    continuum = repo_root / "lean" / "YMGap" / "Continuum"
    continuum.mkdir(parents=True, exist_ok=True)
    summaries: list[str] = []
    for label, chart in [("E8", "A"), ("E9", "A"), ("E8", "B"), ("E9", "B")]:
        data = case_data(label, chart)
        module = module_stem(label, chart)
        shard_count = (
            int(data["degree_x"]) + ROW_SHARD_SIZE
        ) // ROW_SHARD_SIZE
        for shard in range(shard_count):
            path = continuum / f"{module}{shard}.lean"
            path.write_text(render_shard(data, shard))
            certificate_path = continuum / (
                f"HarmonicLowerSixTailEnvelopeCertificate{label}Chart{chart}"
                f"Slice{shard}.lean"
            )
            certificate_path.write_text(render_certificate_slice(data, shard))
        (continuum / f"{module}.lean").write_text(render_umbrella(data))
        summaries.append(
            f"{label}{chart}: degree=({data['degree_x']},{data['degree_y']}), "
            f"shards={shard_count}, table_scale={data['table_scale']}"
        )
    raw_path = continuum / "HarmonicLowerSixTailEnvelopeCertificateRawRows.lean"
    raw_path.write_text(render_raw_rows())
    print("\n".join(summaries))
    print(f"raw={raw_path}")


def main() -> None:
    repo_root = Path(__file__).resolve().parents[1]
    write_all(repo_root)


if __name__ == "__main__":
    main()
