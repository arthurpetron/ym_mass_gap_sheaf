#!/usr/bin/env python3
"""Temporary exact scout for lowering the local-flux certificate thresholds."""

from fractions import Fraction
from math import comb
import gc

from computations import lower_six_tail_second_flux_certificate as cert


def chart_a(poly, threshold):
    terms = [(ij, cert.exact_fraction(c)) for ij, c in poly.terms()]
    degree = max(2 * i + j for (i, j), _ in terms)
    out = {}
    for (i, j), coefficient in terms:
        x_power = degree - (2 * i + j)
        for r_power in range(i + 1):
            key = (x_power, r_power)
            out[key] = out.get(key, Fraction(0)) + coefficient * Fraction(
                comb(i, r_power), threshold**x_power
            )
    return {key: value for key, value in out.items() if value}


def chart_b(poly, threshold):
    terms = [(ij, cert.exact_fraction(c)) for ij, c in poly.terms()]
    degree = max(2 * i + j for (i, j), _ in terms)
    out = {}
    for (i, j), coefficient in terms:
        s_power = degree - (2 * i + j)
        for ell in range(i + 1):
            prefactor = coefficient * Fraction(
                comb(i, ell), threshold**s_power * (2 * threshold) ** ell
            )
            x_power = s_power + ell
            for q in range(ell + 1):
                z_power = i - ell + q
                key = (x_power, z_power)
                value = prefactor * comb(ell, q) * (-1) ** q
                out[key] = out.get(key, Fraction(0)) + value
    return {key: value for key, value in out.items() if value}


def step_chart(poly, threshold, shifted):
    terms = [(ij, cert.exact_fraction(c)) for ij, c in poly.terms()]
    degree = max(i + j for (i, j), _ in terms)
    out = {}
    for (i, j), coefficient in terms:
        x_power = degree - i - j
        if shifted:
            for z_power in range(j + 1):
                key = (x_power, z_power)
                out[key] = out.get(key, Fraction(0)) + coefficient * Fraction(
                    comb(j, z_power), threshold**x_power
                )
        else:
            key = (x_power, j)
            out[key] = out.get(key, Fraction(0)) + coefficient * Fraction(
                1, threshold**x_power
            )
    return {key: value for key, value in out.items() if value}


def minimum(power):
    degree_x = max(a for a, _ in power)
    degree_y = max(b for _, b in power)
    bernstein = cert.bernstein_coefficients(power, degree_x, degree_y)
    result = min(bernstein.items(), key=lambda item: item[1])
    del bernstein
    gc.collect()
    return (degree_x, degree_y), result


def report_chart_a(label, poly, thresholds):
    for threshold in thresholds:
        degree, (index, value) = minimum(chart_a(poly, threshold))
        print(
            f"{label} A={threshold}: degree={degree}, min_index={index}, "
            f"sign={(value > 0) - (value < 0)}, value={value}",
            flush=True,
        )


def report_step(label, poly, thresholds, shifted):
    for threshold in thresholds:
        degree, (index, value) = minimum(step_chart(poly, threshold, shifted))
        print(
            f"{label} T={threshold}: degree={degree}, min_index={index}, "
            f"sign={(value > 0) - (value < 0)}, value={value}",
            flush=True,
        )


def report_chart_b(label, poly, thresholds):
    for threshold in thresholds:
        degree, (index, value) = minimum(chart_b(poly, threshold))
        print(
            f"{label} B={threshold}: degree={degree}, min_index={index}, "
            f"sign={(value > 0) - (value < 0)}, value={value}",
            flush=True,
        )


report_chart_a("L1", cert.sp.Poly(cert.L1NUM, cert.D, cert.n), [11, 12])
report_chart_a("E8", cert.E8_NUM, [11, 12])
report_chart_a("E9", cert.E9_NUM, [11, 12])
report_chart_b("L1", cert.sp.Poly(cert.L1NUM, cert.D, cert.n), [11, 12])
report_chart_b("E8", cert.E8_NUM, [11, 12])
report_chart_b("E9", cert.E9_NUM, [11, 12])
report_step("T9", cert.sp.Poly(cert.L9NUM, cert.D, cert.n), [249], False)
report_step("Base", cert.BASE_FULL_NUM, [249], True)
