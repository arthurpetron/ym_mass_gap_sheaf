#!/usr/bin/env python3
"""
u1_dual_check.py -- U(1) discriminator computation for milestone DP.6 (DP.6-U1 part A).

Model: the boundary complex of the 4-cube (the 3-sphere as a cubical complex):
    8 cubical 3-cells, 24 square faces, 32 edges, 16 vertices;
    every edge is shared by exactly 3 faces (trivalent edge graph).

U(1) dual (Fourier) representation of lattice gauge theory on this complex:
  * plaquette variable = integer charge m_f in Z (character label of U(1));
  * Haar integration over each edge holonomy U_e produces
        integral over U(1) of prod_{f contains e} chi_{m_f}(U_e^{+-1}) dU_e
      = delta( oriented sum of incident charges at e , 0 ),
    i.e. the admissibility constraint is (d2 m)(e) = 0 for every edge e,
    where d2 : C_2 -> C_1 is the cubical boundary operator (rows = edges,
    columns = faces, entries = incidence signs).  Note the prompt's
    "(d^T m)(e)" is the same map written with charges as a column vector on
    faces: the constraint matrix M has M[e,f] = incidence sign of f on e.
  * The dual amplitude of an admissible assignment is EXACTLY 1
    (a product of Kronecker deltas, one per edge); inadmissible = 0.
    There is no recoupling object (no 6j), hence no possible sign.

This script:
  1. builds the cubical chain complex of the 4-cube boundary over Z with
     explicit incidence signs and verifies d o d = 0 (both d1 d2 = 0 and
     d2 d3 = 0, the latter checking orientation bookkeeping against the
     8 three-cells);
  2. computes an exact Z-basis of ker(d2) (the admissible-charge lattice)
     via sympy nullspace over QQ cleared to primitive integer vectors,
     and PROVES it is the full integer kernel (not just a finite-index
     sublattice) by checking the Smith normal form of the basis matrix
     has all invariant factors equal to 1 (saturated => a direct summand
     of Z^24 => equals ker_Z(d2) since the ranks match);
  3. enumerates small kernel vectors (all integer combinations of the
     basis with coefficients in {-1,0,1}: 3^7 = 2187 admissible charge
     assignments, plus random probes) and confirms the dual amplitude is
     identically 1 on the kernel and 0 off it -- at ANY charge,
     structurally: the amplitude formula contains no signed object;
  4. computes the U(1) heat-kernel weighted dual partition sum
         S(s) = sum over admissible m of prod_f s^{m_f^2}
     (U(1) Casimir of charge m is m^2, dimension d_m = 1) restricted to
     the coefficient box |c_i| <= 2 in the kernel basis (5^7 = 78125
     admissible assignments), exactly in Fraction arithmetic at s = 1/2.
     Every term is a positive rational: the truncated sum is manifestly
     a sum of positive terms, and so is every larger truncation --
     the full theta-like series is a monotone limit of positive sums.

Truncation statement (honest): the box |c_i| <= 2 in the specific basis
below is a finite window of the rank-7 admissible lattice; the full sum
adds further terms of the same form s^{sum m_f^2} > 0, so positivity of
the total is structural, not an artifact of the window.  The exact value
reported is the exact value of the WINDOWED sum only.

Contrast pin (SU(2), from the DP program's own computation): the analogous
dual coefficients on this same complex are signed products of 6j symbols;
negatives switch on exactly at plaquette spin n = 3 (j = 3/2, the second
quaternionic irrep), minimal exemplar Z = -1/3981312.  Under heat-kernel
weighting d_n s^{n(n+2)} the positive sector enters at s^3 (n = 1) and the
negative sector at s^15 (n = 3).  Nothing of the sort can happen for U(1):
see the paragraph printed at the end of this script.

Pure Python 3 + sympy (exact QQ/ZZ linear algebra) + fractions.Fraction.
"""

from fractions import Fraction
from itertools import product
import random

import sympy
from sympy import Matrix, ZZ
from sympy.matrices.normalforms import smith_normal_form


# ----------------------------------------------------------------------
# 1. The cubical complex of the 4-cube boundary.
#
# A k-cell of the 4-cube [0,1]^4 is encoded as a length-4 tuple over
# {0, 1, '*'} with exactly k entries equal to '*' (the free coordinates).
# The boundary 3-complex consists of all cells with 0 <= k <= 3 stars.
# ----------------------------------------------------------------------

def cells_with_k_free(k):
    out = []
    for stars in product((0, 1, '*'), repeat=4):
        if stars.count('*') == k:
            out.append(stars)
    return sorted(out, key=lambda c: tuple(str(x) for x in c))


vertices = cells_with_k_free(0)   # 16
edges    = cells_with_k_free(1)   # 32
faces    = cells_with_k_free(2)   # 24
cubes    = cells_with_k_free(3)   # 8  (the facets of the 4-cube)

assert (len(vertices), len(edges), len(faces), len(cubes)) == (16, 32, 24, 8)

v_index = {c: i for i, c in enumerate(vertices)}
e_index = {c: i for i, c in enumerate(edges)}
f_index = {c: i for i, c in enumerate(faces)}
c_index = {c: i for i, c in enumerate(cubes)}


def boundary(cell):
    """Standard cubical boundary with explicit signs.

    Free coordinates a_1 < ... < a_k (positions of '*').
    d(cell) = sum_j (-1)^(j-1) * ( cell|a_j=1  -  cell|a_j=0 ).
    Returns dict {subcell: sign}.
    """
    free = [i for i, x in enumerate(cell) if x == '*']
    out = {}
    for j, a in enumerate(free):          # j = 0-based, sign (-1)^j
        sgn = (-1) ** j
        for val, s2 in ((1, +1), (0, -1)):
            sub = list(cell)
            sub[a] = val
            sub = tuple(sub)
            out[sub] = out.get(sub, 0) + sgn * s2
    return out


def boundary_matrix(higher, lower_index, nrows):
    """Integer matrix of d : C_k -> C_{k-1}; rows = (k-1)-cells, cols = k-cells."""
    M = [[0] * len(higher) for _ in range(nrows)]
    for col, cell in enumerate(higher):
        for sub, sgn in boundary(cell).items():
            M[lower_index[sub]][col] += sgn
    return Matrix(M)


d1 = boundary_matrix(edges, v_index, len(vertices))   # 16 x 32
d2 = boundary_matrix(faces, e_index, len(edges))      # 32 x 24  <-- constraint matrix
d3 = boundary_matrix(cubes, f_index, len(faces))      # 24 x 8

# --- d o d = 0 checks (d2 d3 = 0 is the check "against the 3-cells") ---
dd_12 = d1 * d2
dd_23 = d2 * d3
assert dd_12.is_zero_matrix, "d1 o d2 != 0 -- orientation bookkeeping broken"
assert dd_23.is_zero_matrix, "d2 o d3 != 0 -- orientation bookkeeping broken"
print("d1 o d2 = 0 : VERIFIED  (16x24 zero matrix)")
print("d2 o d3 = 0 : VERIFIED  (32x8 zero matrix, checked against all 8 three-cells)")

# --- trivalence: every edge lies in exactly 3 faces, every incidence sign +-1 ---
for r in range(32):
    row = [d2[r, c] for c in range(24)]
    nz = [x for x in row if x != 0]
    assert len(nz) == 3 and all(abs(x) == 1 for x in nz)
print("edge trivalence : VERIFIED  (every edge has exactly 3 incident faces, signs +-1)")


# ----------------------------------------------------------------------
# 2. The admissible-charge lattice  ker_Z(d2)  (exact).
# ----------------------------------------------------------------------

ns = d2.nullspace()                      # basis of ker over QQ
rank = len(ns)
print(f"\nker(d2) rank over Q : {rank}")
assert rank == 7, "expected rank 7 = (8 cubes) - 1 on S^3"

# clear denominators -> primitive integer vectors
int_basis = []
for v in ns:
    den = sympy.ilcm(*[sympy.fraction(x)[1] for x in v])
    w = [int(x * den) for x in v]
    g = 0
    for x in w:
        g = sympy.igcd(g, x)
    int_basis.append([x // g for x in w])

B = Matrix(24, 7, lambda i, j: int_basis[j][i])       # 24 x 7 integer matrix
assert (d2 * B).is_zero_matrix, "basis vectors not in kernel"

# saturation proof: SNF invariant factors of B all equal 1
snf = smith_normal_form(B, domain=ZZ)
inv = [snf[i, i] for i in range(7)]
assert all(abs(x) == 1 for x in inv), f"basis lattice NOT saturated: {inv}"
print(f"Z-basis of ker(d2)  : 7 columns, Smith invariant factors {inv}")
print("  => the basis generates a SATURATED rank-7 sublattice of Z^24,")
print("     hence equals the FULL integer kernel ker_Z(d2): every admissible")
print("     charge assignment is an integer combination of these 7 vectors.")

# cross-check: rank of d3 is 7 and every cube boundary is admissible
assert d3.rank() == 7
print("cross-check         : rank(d3) = 7 and d2*d3 = 0, so the 8 cube")
print("  boundaries span the same rank-7 lattice (H_2(S^3) = 0: all")
print("  admissible charges are sums of elementary-cube surface charges).")

Bcols = [[int(B[i, j]) for i in range(24)] for j in range(7)]


# ----------------------------------------------------------------------
# 3. Dual amplitudes on and off the kernel.
# ----------------------------------------------------------------------

def amplitude(m):
    """Exact U(1) dual amplitude: product over edges of Kronecker deltas.

    Each edge contributes delta( (d2 m)(e), 0 ).  No other factor exists in
    the abelian dual -- in particular no signed recoupling object.
    Returns 1 (admissible) or 0 (inadmissible).  Never negative, at any charge.
    """
    for r in range(32):
        s = 0
        for c in range(24):
            x = d2[r, c]
            if x:
                s += x * m[c]
        if s != 0:
            return 0
    return 1


def combo(coeffs):
    m = [0] * 24
    for cf, col in zip(coeffs, Bcols):
        if cf:
            for i in range(24):
                m[i] += cf * col[i]
    return m


n_checked = 0
max_abs_charge = 0
for coeffs in product((-1, 0, 1), repeat=7):          # 2187 kernel vectors
    m = combo(coeffs)
    assert amplitude(m) == 1, f"kernel vector with amplitude != 1: {coeffs}"
    n_checked += 1
    max_abs_charge = max(max_abs_charge, max(abs(x) for x in m))
print(f"\nkernel enumeration  : {n_checked} admissible assignments "
      f"(all c in {{-1,0,1}}^7), amplitude == 1 for EVERY one; "
      f"max |m_f| seen = {max_abs_charge}")

rng = random.Random(20260724)
n_off = 0
for _ in range(500):
    m = [rng.randint(-2, 2) for _ in range(24)]
    in_ker = all(
        sum(int(d2[r, c]) * m[c] for c in range(24)) == 0 for r in range(32)
    )
    a = amplitude(m)
    assert a == (1 if in_ker else 0)
    if not in_ker:
        n_off += 1
print(f"random probes       : 500 assignments with |m_f| <= 2; amplitude was 1")
print(f"  exactly on the {500 - n_off} that satisfied the edge constraints and 0 on")
print(f"  the {n_off} that violated at least one edge constraint.  Amplitudes take")
print(f"  values in {{0, 1}} ONLY -- no sign problem, structurally, at any charge.")


# ----------------------------------------------------------------------
# 4. Heat-kernel weighted dual sum at s = 1/2, exact Fractions.
#    weight(m) = prod_f  d_{m_f} s^{Casimir(m_f)} = prod_f s^{m_f^2}
#    (U(1): d_m = 1, Casimir = m^2).
# ----------------------------------------------------------------------

s = Fraction(1, 2)
total = Fraction(0)
by_casimir = {}
n_terms = 0
for coeffs in product((-2, -1, 0, 1, 2), repeat=7):    # 5^7 = 78125 vectors
    m = combo(coeffs)
    cas = sum(x * x for x in m)
    term = s ** cas
    total += term
    by_casimir[cas] = by_casimir.get(cas, 0) + 1
    n_terms += 1

print(f"\nheat-kernel sum     : S(1/2) over the window |c_i| <= 2 "
      f"({n_terms} admissible assignments)")
print(f"  exact value       : {total}")
print(f"                    = {float(total):.15f}")
mins = sorted(k for k in by_casimir if k > 0)[:4]
print(f"  smallest nonzero total Casimirs sum(m_f^2) and multiplicities: "
      f"{[(k, by_casimir[k]) for k in mins]}")
print(f"  every term is s^(sum m_f^2) with s = 1/2 > 0: a POSITIVE rational.")
print(f"  TRUNCATION: this is the exact value of the windowed sum only; the")
print(f"  full rank-7 lattice sum adds further strictly positive terms, so")
print(f"  positivity (and monotone convergence of the theta-like series for")
print(f"  0 < s < 1) is structural and independent of the window.")


# ----------------------------------------------------------------------
# 5. The contrast, stated precisely.
# ----------------------------------------------------------------------

print("""
CONTRAST PIN (SU(2) on the SAME complex, from the DP program):
  dual amplitudes are signed sums of products of 6j symbols; negatives
  switch on exactly at plaquette spin n = 3 (j = 3/2, the second
  quaternionic irrep), minimal exemplar Z = -1/3981312; under heat-kernel
  weighting d_n s^{n(n+2)} the positive sector enters at s^3 and the
  negative sector at s^15.

WHY THIS CANNOT HAPPEN ABELIANLY (the one-paragraph precise statement):
  For U(1) every irrep is 1-dimensional, chi_m . chi_n = chi_{m+n}, so the
  decomposition of a tensor product of irreps is multiplicity-free with a
  SINGLE fusion channel: iterated Clebsch-Gordan fusion of the three
  charges meeting at an edge admits exactly one path, the intertwiner
  space is at most 1-dimensional, and the change of basis between any two
  fusion trees is the identity.  The 6j symbol -- which is precisely the
  overlap between two inequivalent fusion trees -- degenerates to a
  Kronecker delta; there are no two paths to interfere, hence no
  cancellation and no sign.  Each edge integral collapses to
  delta(sum +-m_f, 0) and the amplitude is a product of deltas: 0 or 1.
  For SU(2) the tensor category is non-trivially braided-associated:
  a triple (or higher) fusion has MULTIPLE inequivalent trees, the 6j is
  a genuine unitary change of basis with entries of both signs, and dual
  amplitudes are interference sums over fusion trees.  The sign problem
  observed at j = 3/2 is therefore an intrinsically NON-ABELIAN
  phenomenon: it is the interference of fusion paths, an object that does
  not exist over any abelian group.
""")

print("ALL CHECKS PASSED.")
