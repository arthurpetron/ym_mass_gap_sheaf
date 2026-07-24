"""Exact SU(2) Haar-network arithmetic in quaternion coordinates.

This module evaluates polynomial character networks without floating point.
It is the executable counterpart of the repository's constructive SU(2)
character/Haar spine:

* representations use the doubled spin label ``n = 2j``;
* ``dim(n) = n + 1`` and ``casimir4(n) = 4 C_2(j) = n(n + 2)``;
* a group element is a unit quaternion ``(w, x, y, z)``;
* normalized Haar measure is normalized surface measure on ``S^3``;
* ``chi(n, q)`` is the Chebyshev-U character, with
  ``chi(0) = 1``, ``chi(1) = 2w`` and
  ``chi(n + 1) = 2w chi(n) - chi(n - 1)``.

The heat-kernel coordinate is ``s = exp(-t/4)``.  Consequently a spin-``n``
term has the integral exponent ``n(n + 2)``.  Coefficients are sparse exact
polynomials in ``s``; coordinate coefficients and every Haar moment are
``fractions.Fraction`` values.

The graph evaluator is genuine: shared links are represented by the same four
quaternion-coordinate variables, all character factors are multiplied, and
each link is integrated with the exact normalized ``S^3`` moment.  No pinned
network values or topology-specific contraction tables occur here.
"""

from __future__ import annotations

from collections.abc import Iterable, Sequence
from fractions import Fraction
from functools import cache
from math import factorial, prod
from typing import Any, Literal, TypeAlias

# Exact univariate polynomials in the heat-kernel coordinate s.
SPoly: TypeAlias = dict[int, Fraction]
SparsePoly: TypeAlias = SPoly

S_ONE: SPoly = {0: Fraction(1)}


def _check_power(power: int) -> None:
    if power < 0:
        raise ValueError(f"polynomial power must be nonnegative; got {power}")


def sp_clean(p: SPoly) -> SPoly:
    """Return the canonical sparse form, dropping zero coefficients."""
    out: SPoly = {}
    for power, coefficient in p.items():
        _check_power(power)
        if coefficient:
            out[power] = Fraction(coefficient)
    return out


def sp_scale(p: SPoly, coefficient: Fraction) -> SPoly:
    """Scale an exact ``s``-polynomial."""
    if coefficient == 0:
        return {}
    return {power: value * coefficient for power, value in sp_clean(p).items()}


def sp_add_into(
    accumulator: SPoly,
    p: SPoly,
    coefficient: Fraction = Fraction(1),
) -> None:
    """Add ``coefficient * p`` to ``accumulator`` in place."""
    if coefficient == 0:
        return
    for power, value in sp_clean(p).items():
        new_value = accumulator.get(power, Fraction(0)) + value * coefficient
        if new_value:
            accumulator[power] = new_value
        else:
            accumulator.pop(power, None)


def sp_add(a: SPoly, b: SPoly) -> SPoly:
    """Add two exact ``s``-polynomials."""
    out = sp_clean(a)
    sp_add_into(out, b)
    return out


def sp_mul(a: SPoly, b: SPoly) -> SPoly:
    """Multiply two exact ``s``-polynomials."""
    out: SPoly = {}
    for power_a, value_a in sp_clean(a).items():
        for power_b, value_b in sp_clean(b).items():
            power = power_a + power_b
            new_value = out.get(power, Fraction(0)) + value_a * value_b
            if new_value:
                out[power] = new_value
            else:
                out.pop(power, None)
    return out


def sp_shift(p: SPoly, power: int) -> SPoly:
    """Multiply an exact ``s``-polynomial by ``s**power``."""
    _check_power(power)
    return {old_power + power: value for old_power, value in sp_clean(p).items()}


def sp_pow(p: SPoly, exponent: int) -> SPoly:
    """Raise an exact ``s``-polynomial to a nonnegative integer power."""
    if exponent < 0:
        raise ValueError(f"polynomial exponent must be nonnegative; got {exponent}")
    result = dict(S_ONE)
    factor = sp_clean(p)
    remaining = exponent
    while remaining:
        if remaining % 2:
            result = sp_mul(result, factor)
        factor = sp_mul(factor, factor)
        remaining //= 2
    return result


def sp_eval(p: SPoly, s: Fraction) -> Fraction:
    """Evaluate an exact ``s``-polynomial at a rational point."""
    return sum(
        (coefficient * s**power for power, coefficient in sp_clean(p).items()),
        start=Fraction(0),
    )


# Coordinate polynomials.  Variable ``4 * link + component`` is component
# 0,1,2,3 = w,x,y,z of that link.  Monomials are sorted sparse exponent rows.
Mono: TypeAlias = tuple[tuple[int, int], ...]
Poly: TypeAlias = dict[Mono, SPoly]
Quat: TypeAlias = tuple[Poly, Poly, Poly, Poly]
OrientedPath: TypeAlias = Sequence[tuple[int, int]]

P_ZERO: Poly = {}


def p_const(p: SPoly) -> Poly:
    """Embed an exact ``s``-polynomial as a coordinate constant."""
    clean = sp_clean(p)
    return {(): clean} if clean else {}


P_ONE: Poly = p_const(S_ONE)
Q_ID: Quat = (P_ONE, P_ZERO, P_ZERO, P_ZERO)


def p_var(link: int, component: int) -> Poly:
    """Construct one quaternion-coordinate variable."""
    if link < 0:
        raise ValueError(f"link index must be nonnegative; got {link}")
    if component not in range(4):
        raise ValueError(f"quaternion component must be 0, 1, 2 or 3; got {component}")
    return {((4 * link + component, 1),): dict(S_ONE)}


def mono_mul(a: Mono, b: Mono) -> Mono:
    """Multiply two sparse coordinate monomials."""
    if not a:
        return b
    if not b:
        return a
    powers = dict(a)
    for variable, exponent in b:
        powers[variable] = powers.get(variable, 0) + exponent
    return tuple(sorted(powers.items()))


def p_add_into(
    accumulator: Poly,
    p: Poly,
    coefficient: Fraction = Fraction(1),
) -> None:
    """Add ``coefficient * p`` to a coordinate polynomial in place."""
    if coefficient == 0:
        return
    for monomial, s_poly in p.items():
        slot = accumulator.setdefault(monomial, {})
        sp_add_into(slot, s_poly, coefficient)
        if not slot:
            del accumulator[monomial]


def p_neg(p: Poly) -> Poly:
    """Negate a coordinate polynomial."""
    return {monomial: sp_scale(s_poly, Fraction(-1)) for monomial, s_poly in p.items()}


def p_scale_s(
    p: Poly,
    s_power: int,
    coefficient: Fraction = Fraction(1),
) -> Poly:
    """Multiply a coordinate polynomial by ``coefficient * s**s_power``."""
    _check_power(s_power)
    if coefficient == 0:
        return {}
    return {
        monomial: sp_shift(sp_scale(s_poly, coefficient), s_power) for monomial, s_poly in p.items()
    }


def p_mul(a: Poly, b: Poly) -> Poly:
    """Multiply two coordinate polynomials exactly."""
    out: Poly = {}
    for monomial_a, s_poly_a in a.items():
        for monomial_b, s_poly_b in b.items():
            monomial = mono_mul(monomial_a, monomial_b)
            product = sp_mul(s_poly_a, s_poly_b)
            slot = out.setdefault(monomial, {})
            sp_add_into(slot, product)
            if not slot:
                del out[monomial]
    return out


def p_reduce_units(p: Poly) -> Poly:
    """Reduce modulo ``w² + x² + y² + z² = 1`` on every link.

    The chosen normal form eliminates every ``z`` exponent at least two using
    ``z² = 1 - w² - x² - y²``.  This is useful when comparing expressions
    before all links have been integrated.
    """
    work: Poly = {monomial: dict(s_poly) for monomial, s_poly in p.items() if sp_clean(s_poly)}
    out: Poly = {}
    while work:
        monomial, s_poly = work.popitem()
        target: tuple[int, int] | None = None
        for variable, exponent in monomial:
            if variable % 4 == 3 and exponent >= 2:
                target = (variable, exponent)
                break
        if target is None:
            p_add_into(out, {monomial: s_poly})
            continue

        variable, exponent = target
        base = variable - 3
        rest = tuple((var, exp) for var, exp in monomial if var != variable)
        low = mono_mul(rest, ((variable, exponent - 2),)) if exponent > 2 else rest
        substitutions: tuple[tuple[Mono, int], ...] = (
            ((), 1),
            (((base, 2),), -1),
            (((base + 1, 2),), -1),
            (((base + 2, 2),), -1),
        )
        for substitution, sign in substitutions:
            new_monomial = mono_mul(low, substitution)
            p_add_into(work, {new_monomial: s_poly}, Fraction(sign))
    return out


def p_equal_on_group(a: Poly, b: Poly) -> bool:
    """Decide exact equality as functions on a product of SU(2) copies."""
    difference = {monomial: dict(s_poly) for monomial, s_poly in a.items()}
    p_add_into(difference, b, Fraction(-1))
    return p_reduce_units(difference) == {}


def p_links(p: Poly) -> set[int]:
    """Return the set of link variables occurring in a polynomial."""
    return {variable // 4 for monomial in p for variable, _exponent in monomial}


def q_link(link: int) -> Quat:
    """The generic unit quaternion assigned to ``link``."""
    return p_var(link, 0), p_var(link, 1), p_var(link, 2), p_var(link, 3)


def q_conj(q: Quat) -> Quat:
    """Quaternion conjugation, corresponding to group inversion."""
    return q[0], p_neg(q[1]), p_neg(q[2]), p_neg(q[3])


def _q_component(terms: Sequence[tuple[Poly, Poly, int]]) -> Poly:
    out: Poly = {}
    for a, b, sign in terms:
        p_add_into(out, p_mul(a, b), Fraction(sign))
    return out


def q_mul(a: Quat, b: Quat) -> Quat:
    """Hamilton multiplication of polynomial-valued quaternions."""
    w1, x1, y1, z1 = a
    w2, x2, y2, z2 = b
    return (
        _q_component(((w1, w2, 1), (x1, x2, -1), (y1, y2, -1), (z1, z2, -1))),
        _q_component(((w1, x2, 1), (x1, w2, 1), (y1, z2, 1), (z1, y2, -1))),
        _q_component(((w1, y2, 1), (y1, w2, 1), (z1, x2, 1), (x1, z2, -1))),
        _q_component(((w1, z2, 1), (z1, w2, 1), (x1, y2, 1), (y1, x2, -1))),
    )


def holonomy(path: OrientedPath) -> Quat:
    """Return the ordered holonomy of ``(link, orientation)`` steps."""
    result = Q_ID
    for link, orientation in path:
        if orientation not in (-1, 1):
            raise ValueError(f"edge orientation must be +1 or -1; got {orientation}")
        edge = q_link(link)
        result = q_mul(result, edge if orientation == 1 else q_conj(edge))
    return result


def _check_label(label: int) -> None:
    if label < 0:
        raise ValueError(f"doubled SU(2) label must be nonnegative; got {label}")


def dimension(label: int) -> int:
    """Dimension of the doubled-label SU(2) irrep: ``label + 1``."""
    _check_label(label)
    return label + 1


def dim(label: int) -> int:
    """Compatibility alias for :func:`dimension`."""
    return dimension(label)


def casimir(label: int) -> Fraction:
    """Quadratic Casimir ``j(j+1)`` for doubled label ``label = 2j``."""
    _check_label(label)
    return Fraction(label * (label + 2), 4)


def casimir4(label: int) -> int:
    """The integral heat exponent ``4 C_2 = label(label+2)``."""
    _check_label(label)
    return label * (label + 2)


def admissible(a: int, b: int, c: int) -> bool:
    """SU(2) trivalent admissibility in doubled labels."""
    _check_label(a)
    _check_label(b)
    _check_label(c)
    return abs(a - b) <= c <= a + b and (a + b + c) % 2 == 0


def fusion_labels(a: int, b: int) -> tuple[int, ...]:
    """The multiplicity-free labels in ``a tensor b``."""
    _check_label(a)
    _check_label(b)
    return tuple(range(abs(a - b), a + b + 1, 2))


def invariant_multiplicity(labels: Sequence[int]) -> int:
    """Multiplicity of the trivial representation in a tensor product."""
    packet: dict[int, int] = {0: 1}
    for label in labels:
        _check_label(label)
        next_packet: dict[int, int] = {}
        for intermediate, multiplicity in packet.items():
            for output in fusion_labels(intermediate, label):
                next_packet[output] = next_packet.get(output, 0) + multiplicity
        packet = next_packet
    return packet.get(0, 0)


def chi(label: int, q: Quat) -> Poly:
    """The exact character ``chi_label(q)`` for doubled spin ``label``."""
    _check_label(label)
    if label == 0:
        return {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}
    two_w: Poly = {}
    p_add_into(two_w, q[0], Fraction(2))
    previous = {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}
    current = two_w
    for _ in range(label - 1):
        following = p_mul(two_w, current)
        p_add_into(following, previous, Fraction(-1))
        previous, current = current, following
    return current


def heat_activity(q: Quat, nmax: int) -> Poly:
    """Truncated ``sum_n dim(n) s^(4C2(n)) chi_n(q)``."""
    if nmax < 0:
        raise ValueError(f"spin cutoff must be nonnegative; got {nmax}")
    out: Poly = {}
    for label in range(nmax + 1):
        term = p_scale_s(
            chi(label, q),
            casimir4(label),
            Fraction(dimension(label)),
        )
        p_add_into(out, term)
    return out


@cache
def _odd_double_factorial(half_exponent: int) -> int:
    """Return ``(2k-1)!!``, with ``(-1)!! = 1`` at ``k = 0``."""
    if half_exponent < 0:
        raise ValueError("half exponent must be nonnegative")
    product = 1
    for index in range(1, half_exponent + 1):
        product *= 2 * index - 1
    return product


@cache
def haar_s3_moment(exponents: tuple[int, int, int, int]) -> Fraction:
    """Normalized ``S^3`` moment of ``w^a x^b y^c z^d``.

    Odd coordinate powers vanish.  For exponents ``2a_i``, the value is

    ``prod_i (2a_i-1)!! / (2^A (A+1)!)``, where ``A = sum_i a_i``.
    """
    if any(exponent < 0 for exponent in exponents):
        raise ValueError(f"moment exponents must be nonnegative; got {exponents}")
    if any(exponent % 2 for exponent in exponents):
        return Fraction(0)
    halves = tuple(exponent // 2 for exponent in exponents)
    total = sum(halves)
    numerator = 1
    for half_exponent in halves:
        numerator *= _odd_double_factorial(half_exponent)
    denominator = (2**total) * factorial(total + 1)
    return Fraction(numerator, denominator)


def integrate_link(p: Poly, link: int) -> Poly:
    """Integrate one link against normalized SU(2) Haar measure."""
    if link < 0:
        raise ValueError(f"link index must be nonnegative; got {link}")
    base = 4 * link
    out: Poly = {}
    for monomial, s_poly in p.items():
        exponents = [0, 0, 0, 0]
        rest: list[tuple[int, int]] = []
        for variable, exponent in monomial:
            if base <= variable < base + 4:
                exponents[variable - base] = exponent
            else:
                rest.append((variable, exponent))
        moment = haar_s3_moment((exponents[0], exponents[1], exponents[2], exponents[3]))
        if moment:
            p_add_into(out, {tuple(rest): s_poly}, moment)
    return out


def link_linear_coefficients(p: Poly, link: int) -> tuple[Poly, Poly, Poly, Poly]:
    """Write a link-linear polynomial as ``sum_a coefficient[a] * q[a]``.

    Every monomial must contain exactly one coordinate of ``link`` to the
    first power.  Coefficients may be arbitrary polynomials in all other
    links.  A ``ValueError`` prevents accidental use on a factor with a
    constant, quadratic, or higher link dependence.
    """

    if link < 0:
        raise ValueError(f"link index must be nonnegative; got {link}")
    base = 4 * link
    coefficients: list[Poly] = [{}, {}, {}, {}]
    for monomial, s_poly in p.items():
        selected: int | None = None
        rest: list[tuple[int, int]] = []
        for variable, exponent in monomial:
            if base <= variable < base + 4:
                if selected is not None or exponent != 1:
                    raise ValueError("factor is not linear in the requested link")
                selected = variable - base
            else:
                rest.append((variable, exponent))
        if selected is None:
            raise ValueError("factor has a link-independent monomial")
        p_add_into(coefficients[selected], {tuple(rest): s_poly})
    return coefficients[0], coefficients[1], coefficients[2], coefficients[3]


def integrate_link_linear_factors(
    factors: Sequence[Poly],
    link: int,
) -> Poly:
    """Integrate link-linear factors by the exact S^3 pairing law.

    If ``f_i(q) = c_i dot q`` and there are ``2m`` factors, normalized
    surface measure on ``S^3`` gives

    ``integral product_i f_i(q)
       = sum_pairings product_(i,j) (c_i dot c_j)
         / (4 * 6 * ... * (2m + 2))``.

    Contracting this Haar projector before multiplying every coordinate
    factor avoids the large generic intermediate at a high-valence
    fundamental link.
    """

    if link < 0:
        raise ValueError(f"link index must be nonnegative; got {link}")
    if not factors:
        return {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}
    if len(factors) % 2:
        # Validate the factors even though every odd S^3 moment vanishes.
        for factor in factors:
            link_linear_coefficients(factor, link)
        return {}

    coefficients = tuple(link_linear_coefficients(factor, link) for factor in factors)
    dot_products: dict[tuple[int, int], Poly] = {}
    for left in range(len(factors)):
        for right in range(left + 1, len(factors)):
            dot: Poly = {}
            for component in range(4):
                p_add_into(
                    dot,
                    p_mul(
                        coefficients[left][component],
                        coefficients[right][component],
                    ),
                )
            dot_products[(left, right)] = dot

    moments: dict[int, Poly] = {0: {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}}

    def pairing_sum(mask: int) -> Poly:
        cached = moments.get(mask)
        if cached is not None:
            return cached
        first_bit = mask & -mask
        first = first_bit.bit_length() - 1
        rest = mask ^ first_bit
        out: Poly = {}
        remaining = rest
        while remaining:
            partner_bit = remaining & -remaining
            partner = partner_bit.bit_length() - 1
            pair = min(first, partner), max(first, partner)
            p_add_into(
                out,
                p_mul(
                    dot_products[pair],
                    pairing_sum(rest ^ partner_bit),
                ),
            )
            remaining ^= partner_bit
        moments[mask] = out
        return out

    full_mask = (1 << len(factors)) - 1
    half_count = len(factors) // 2
    denominator = prod(4 + 2 * index for index in range(half_count))
    out: Poly = {}
    p_add_into(
        out,
        pairing_sum(full_mask),
        Fraction(1, denominator),
    )
    return out


def contract(factors: Iterable[Poly], links: Iterable[int]) -> Poly:
    """Multiply factors and exactly Haar-integrate the requested links.

    A deterministic greedy variable-elimination order minimizes the product
    of the sizes of all factors incident to the next link.
    """
    remaining_factors = list(factors)
    pending = set(links)
    if any(link < 0 for link in pending):
        raise ValueError(f"link indices must be nonnegative; got {pending}")

    while pending:
        choices: list[tuple[int, int, list[int]]] = []
        for link in sorted(pending):
            indices = [
                index for index, factor in enumerate(remaining_factors) if link in p_links(factor)
            ]
            cost = 1
            for index in indices:
                cost *= max(1, len(remaining_factors[index]))
            choices.append((cost, link, indices))
        _cost, selected_link, selected_indices = min(choices)

        merged = {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}
        kept: list[Poly] = []
        selected = set(selected_indices)
        for index, factor in enumerate(remaining_factors):
            if index in selected:
                merged = p_mul(merged, factor)
            else:
                kept.append(factor)
        kept.append(integrate_link(merged, selected_link))
        remaining_factors = kept
        pending.remove(selected_link)

    out = {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}
    for factor in remaining_factors:
        out = p_mul(out, factor)
    return out


def contract_pairing_aware(factors: Iterable[Poly], links: Iterable[int]) -> Poly:
    """Contract a network while preserving fundamental-strand factors.

    Whenever every factor incident to a link is linear in that link, the
    exact spherical pairing projector is applied before the factors are
    multiplied.  This is the coordinate realization of contracting the
    local fundamental intertwiner block.  Composite factors produced later
    in the elimination may cease to be link-linear; those links fall back to
    the generic exact Haar moment without changing the value.

    Linear links are eliminated before generic links.  Within each class the
    same deterministic factor-size cost as :func:`contract` is used.
    """

    remaining_factors = list(factors)
    pending = set(links)
    if any(link < 0 for link in pending):
        raise ValueError(f"link indices must be nonnegative; got {pending}")

    while pending:
        choices: list[tuple[int, int, int, list[int]]] = []
        for link in sorted(pending):
            indices = [
                index for index, factor in enumerate(remaining_factors) if link in p_links(factor)
            ]
            linear = True
            for index in indices:
                try:
                    link_linear_coefficients(remaining_factors[index], link)
                except ValueError:
                    linear = False
                    break
            cost = 1
            for index in indices:
                cost *= max(1, len(remaining_factors[index]))
            choices.append((int(not linear), cost, link, indices))
        generic, _cost, selected_link, selected_indices = min(choices)

        kept: list[Poly] = []
        selected = set(selected_indices)
        incident: list[Poly] = []
        for index, factor in enumerate(remaining_factors):
            if index in selected:
                incident.append(factor)
            else:
                kept.append(factor)
        if not generic:
            kept.append(integrate_link_linear_factors(incident, selected_link))
        else:
            merged = {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}
            for factor in incident:
                merged = p_mul(merged, factor)
            kept.append(integrate_link(merged, selected_link))
        remaining_factors = kept
        pending.remove(selected_link)

    out = {monomial: dict(s_poly) for monomial, s_poly in P_ONE.items()}
    for factor in remaining_factors:
        out = p_mul(out, factor)
    return out


def scalar(p: Poly) -> SPoly:
    """Extract a fully contracted coordinate constant."""
    leftovers = [monomial for monomial in p if monomial]
    if leftovers:
        raise ValueError(f"network not fully contracted: leftover {leftovers[0]}")
    return dict(p.get((), {}))


def haar_character_network(
    faces: Sequence[OrientedPath],
    labels: Sequence[int],
    edge_count: int | None = None,
) -> Fraction:
    """Evaluate a closed product of face characters by direct Haar integration.

    This convenience entry point carries no heat coordinate; for a symbolic
    heat-kernel network use :func:`chi`, :func:`heat_activity` and
    :func:`contract` directly.
    """
    if len(faces) != len(labels):
        raise ValueError("faces and labels must have the same length")
    largest_edge = max(
        (edge for face in faces for edge, _orientation in face),
        default=-1,
    )
    inferred_count = largest_edge + 1
    count = inferred_count if edge_count is None else edge_count
    if count < inferred_count or count < 0:
        raise ValueError(f"edge_count {count} does not contain inferred {inferred_count} edges")
    factors = [
        chi(label, holonomy(face)) for face, label in zip(faces, labels, strict=True) if label > 0
    ]
    value = scalar(contract(factors, range(count)))
    if any(power != 0 for power in value):
        raise AssertionError(f"character-only network acquired heat powers: {value}")
    return value.get(0, Fraction(0))


class GaugeFixedComplex:
    """A connected one-complex with maximal-tree gauge fixing.

    Gauge-invariant closed-loop factors may set every spanning-tree link to
    the identity by Haar invariance.  Only co-tree links remain as integration
    variables.
    """

    def __init__(self, n_vertices: int, edges: Sequence[tuple[int, int]]) -> None:
        if n_vertices <= 0:
            raise ValueError("a complex must contain at least one vertex")
        self.edges = list(edges)
        adjacency: dict[int, list[tuple[int, int]]] = {vertex: [] for vertex in range(n_vertices)}
        for edge_index, (tail, head) in enumerate(self.edges):
            if tail not in adjacency or head not in adjacency:
                raise ValueError(f"edge {(tail, head)} leaves the vertex set")
            adjacency[tail].append((head, edge_index))
            adjacency[head].append((tail, edge_index))

        tree: set[int] = set()
        seen = {0}
        frontier = [0]
        while frontier:
            next_frontier: list[int] = []
            for vertex in frontier:
                for neighbor, edge_index in adjacency[vertex]:
                    if neighbor not in seen:
                        seen.add(neighbor)
                        tree.add(edge_index)
                        next_frontier.append(neighbor)
            frontier = next_frontier
        if len(seen) != n_vertices:
            raise ValueError("complex is not connected")
        self.tree = tree
        self.free = [edge_index for edge_index in range(len(self.edges)) if edge_index not in tree]

    def edge_quat(self, edge_index: int, orientation: int) -> Quat:
        """Return a gauge-fixed oriented edge quaternion."""
        if edge_index not in range(len(self.edges)):
            raise ValueError(f"edge index out of range: {edge_index}")
        if orientation not in (-1, 1):
            raise ValueError(f"edge orientation must be +1 or -1; got {orientation}")
        if edge_index in self.tree:
            return Q_ID
        edge = q_link(edge_index)
        return edge if orientation == 1 else q_conj(edge)

    def _check_closed(self, path: OrientedPath) -> None:
        if not path:
            return
        first_edge, first_orientation = path[0]
        if first_edge not in range(len(self.edges)) or first_orientation not in (-1, 1):
            raise ValueError("invalid first oriented edge")
        first_tail, first_head = self.edges[first_edge]
        start = first_tail if first_orientation == 1 else first_head
        current = first_head if first_orientation == 1 else first_tail
        for edge_index, orientation in path[1:]:
            if edge_index not in range(len(self.edges)) or orientation not in (-1, 1):
                raise ValueError(f"invalid oriented edge {(edge_index, orientation)}")
            tail, head = self.edges[edge_index]
            step_tail = tail if orientation == 1 else head
            step_head = head if orientation == 1 else tail
            if current != step_tail:
                raise ValueError(f"path is discontinuous at edge {edge_index}")
            current = step_head
        if current != start:
            raise ValueError("path is not closed")

    def holonomy_of(self, path: OrientedPath) -> Quat:
        """Build the exact holonomy of a closed oriented path."""
        self._check_closed(path)
        result = Q_ID
        for edge_index, orientation in path:
            result = q_mul(result, self.edge_quat(edge_index, orientation))
        return result

    def contract_invariant(self, factors: Iterable[Poly]) -> SPoly:
        """Contract gauge-invariant factors over the co-tree links."""
        return scalar(contract(factors, self.free))


Point: TypeAlias = tuple[int, ...]
FaceMetadata: TypeAlias = tuple[Point, int, int]


def brick_complex_nd(
    dimensions: Sequence[int],
) -> tuple[
    GaugeFixedComplex,
    list[list[tuple[int, int]]],
    list[FaceMetadata],
]:
    """Construct all oriented plaquettes of an axis-aligned lattice brick.

    ``dimensions[d]`` is the number of unit intervals in coordinate direction
    ``d``.  Edges point in the positive coordinate direction.  A face with
    metadata ``(point, d1, d2)`` is based at ``point``, has ``d1 < d2``, and is
    traversed in the orientation ``+d1, +d2, -d1, -d2``.

    The vertex, edge, and face iteration orders extend the historical 3D
    builder exactly: the first coordinate is outermost and the last is
    innermost.  This makes the metadata suitable for reproducible
    classification under coordinate symmetries.
    """
    shape = tuple(dimensions)
    if not shape:
        raise ValueError("a brick must have at least one dimension")
    if any(length < 0 for length in shape):
        raise ValueError("brick dimensions must be nonnegative")

    from itertools import product

    points = product(*(range(length + 1) for length in shape))
    vertices: dict[Point, int] = {point: index for index, point in enumerate(points)}

    edges: list[tuple[int, int]] = []
    edge_ids: dict[tuple[Point, Point], int] = {}

    def step(point: Point, direction: int) -> Point:
        return tuple(coordinate + int(axis == direction) for axis, coordinate in enumerate(point))

    def add_edge(tail: Point, head: Point) -> int:
        key = tail, head
        if key not in edge_ids:
            edge_ids[key] = len(edges)
            edges.append((vertices[tail], vertices[head]))
        return edge_ids[key]

    for point in vertices:
        for direction in range(len(shape)):
            neighbor = step(point, direction)
            if neighbor in vertices:
                add_edge(point, neighbor)

    faces: list[list[tuple[int, int]]] = []
    metadata: list[FaceMetadata] = []
    for point in vertices:
        for first_direction in range(len(shape)):
            for second_direction in range(first_direction + 1, len(shape)):
                first = step(point, first_direction)
                diagonal = step(first, second_direction)
                second = step(point, second_direction)
                if first in vertices and diagonal in vertices and second in vertices:
                    faces.append(
                        [
                            (add_edge(point, first), 1),
                            (add_edge(first, diagonal), 1),
                            (add_edge(second, diagonal), -1),
                            (add_edge(point, second), -1),
                        ]
                    )
                    metadata.append((point, first_direction, second_direction))
    return GaugeFixedComplex(len(vertices), edges), faces, metadata


def brick_complex(
    nx: int,
    ny: int,
    nz: int,
) -> tuple[GaugeFixedComplex, list[list[tuple[int, int]]]]:
    """Construct the oriented faces of ``[0,nx] x [0,ny] x [0,nz]``."""
    complex_, faces, _metadata = brick_complex_nd((nx, ny, nz))
    return complex_, faces


def sp_str(p: SPoly) -> str:
    """Format an exact ``s``-polynomial for reports."""
    clean = sp_clean(p)
    if not clean:
        return "0"
    terms = [
        f"{coefficient}" if power == 0 else f"{coefficient}*s^{power}"
        for power, coefficient in sorted(clean.items())
    ]
    return " + ".join(terms).replace("+ -", "- ")


SignVerdict: TypeAlias = Literal["zero", "positive", "negative", "mixed"]


def sign_on_unit_interval(p: SPoly) -> SignVerdict:
    """Give the exact sign class on the open interval ``0 < s < 1``.

    ``positive`` and ``negative`` mean a constant weak sign with a nonzero
    value somewhere; isolated even-multiplicity zeros retain that verdict.
    ``mixed`` means both signs occur.  The decision uses exact square-free
    factorization and Sturm root counting over ``QQ``.
    """
    clean = sp_clean(p)
    if not clean:
        return "zero"
    if all(coefficient > 0 for coefficient in clean.values()):
        return "positive"
    if all(coefficient < 0 for coefficient in clean.values()):
        return "negative"

    import sympy

    variable: Any = sympy.Symbol("s")
    expression: Any = sum(
        (
            sympy.Rational(coefficient.numerator, coefficient.denominator) * variable**power
            for power, coefficient in clean.items()
        ),
        start=sympy.Integer(0),
    )
    polynomial: Any = sympy.Poly(sympy.expand(expression), variable, domain=sympy.QQ)
    _content, factors = polynomial.sqf_list()
    odd_part: Any = sympy.Poly(1, variable, domain=sympy.QQ)
    for factor, multiplicity in factors:
        if multiplicity % 2:
            odd_part *= factor

    roots_closed: int = int(odd_part.count_roots(0, 1))
    roots_open = roots_closed - int(odd_part.eval(0) == 0) - int(odd_part.eval(1) == 0)
    if roots_open:
        return "mixed"

    # The lowest nonzero coefficient is the sign immediately to the right of
    # zero.  With no odd-multiplicity root in (0,1), that is the global sign
    # away from isolated even-multiplicity zeros.
    leading_at_zero = clean[min(clean)]
    return "positive" if leading_at_zero > 0 else "negative"
