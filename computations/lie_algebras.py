"""General simple-Lie-algebra engine: dimensions, quadratic Casimirs, and the
heat-kernel character sum `Z_t`, for every compact simple gauge group.

Milestone U.4 (`docs/uniform-parametric-bound-plan.md`): the SU(2)/SU(3)
character sums (`large_field_kp`, `su3_character_sum`) are hardcoded; to test
the *uniform parametric bound* strategy — that SU(2) is the worst case for the
σ̂-budget — we need `Σ η(G)` for all nine types (A,B,C,D + G₂,F₄,E₆,E₇,E₈).
This module computes, from Cartan data alone:

  * `dim(λ)`  via the Weyl dimension formula,
  * `C₂(λ)`   the quadratic Casimir `½⟨λ, λ+2ρ⟩`,
  * `Z_t`     `= Σ_{λ≠0} dim(λ)²·exp(-t·C₂(λ))` over dominant weights.

Normalization is fixed (global scale ½) so that it reproduces the project's
convention exactly: `C₂(adj) = h∨` (dual Coxeter number) and, for SU(N),
`C₂(fund) = (N²-1)/(2N)` — i.e. SU(2)→3/4, SU(3)→4/3.  The self-test
(`__main__`) verifies `C₂(adj)=h∨` and `dim(adj)=dim(G)` for all types.

Weights are in the fundamental-weight (Dynkin-label) basis; roots in the
simple-root basis.  `ρ = (1,…,1)` in the Dynkin basis.
"""

from __future__ import annotations

import math
from dataclasses import dataclass

import numpy as np


# ---------------------------------------------------------------------------
# Cartan matrices A and symmetrizers d (long simple roots have d = 1).
# Convention check enforced in `_validate`: A_{ij}·d_j is symmetric.
# ---------------------------------------------------------------------------

def _cartan(kind: str, n: int) -> tuple[np.ndarray, np.ndarray]:
    """Return (Cartan matrix A, symmetrizer d) for a simple type.

    `kind ∈ {A,B,C,D,E,F,G}`; `n` = rank.  Bourbaki node conventions.
    """
    A = np.zeros((n, n))
    for i in range(n):
        A[i, i] = 2.0
    d = np.ones(n)

    if kind == "A":
        for i in range(n - 1):
            A[i, i + 1] = A[i + 1, i] = -1.0
    elif kind == "D":
        for i in range(n - 2):
            A[i, i + 1] = A[i + 1, i] = -1.0
        # node n attaches to node n-2 (fork); 1-indexed nodes n-1,n -> idx n-2 fork
        A[n - 3, n - 1] = A[n - 1, n - 3] = -1.0
    elif kind == "E":
        # E_n: chain 1-2-3-4-... with node "2" carrying the branch to node n.
        # Bourbaki labelling: branch node is α_2 (index 1) -> α_4 (index 3) chain;
        # use the standard E6/E7/E8 Dynkin diagram.
        # Nodes (1-indexed): 1-3-4-5-6[-7[-8]] chain, with 2 attached to 4.
        chain = [1, 3, 4, 5, 6, 7, 8][:n - 1]  # the long chain (1-indexed), len n-1
        for a, b in zip(chain, chain[1:]):
            A[a - 1, b - 1] = A[b - 1, a - 1] = -1.0
        A[1, 3] = A[3, 1] = -1.0  # node 2 (idx1) attaches to node 4 (idx3)
    elif kind == "B":  # α_n short
        for i in range(n - 1):
            A[i, i + 1] = A[i + 1, i] = -1.0
        A[n - 2, n - 1] = -2.0  # long row, short col
        A[n - 1, n - 2] = -1.0
        d[n - 1] = 0.5
    elif kind == "C":  # α_n long, α_1..α_{n-1} short
        for i in range(n - 1):
            A[i, i + 1] = A[i + 1, i] = -1.0
        A[n - 1, n - 2] = -2.0  # long row, short col
        A[n - 2, n - 1] = -1.0
        d[: n - 1] = 0.5
    elif kind == "F":  # F4: α1,α2 long; α3,α4 short
        A[0, 1] = A[1, 0] = -1.0
        A[1, 2] = -2.0
        A[2, 1] = -1.0
        A[2, 3] = A[3, 2] = -1.0
        d[2] = d[3] = 0.5
    elif kind == "G":  # G2: α1 short, α2 long
        A[0, 1] = -1.0
        A[1, 0] = -3.0
        d[0] = 1.0 / 3.0
    else:
        raise ValueError(f"unknown kind {kind}")
    return A, d


def _positive_roots(A: np.ndarray) -> list[np.ndarray]:
    """All positive roots in the simple-root basis, by the height-building
    algorithm: for root β and simple α_i, the α_i-string gives q = p - ⟨β,α_i∨⟩
    where p counts how many times β-kα_i (k≥1) is already a root."""
    n = A.shape[0]
    simple = [np.eye(n)[i].astype(int) for i in range(n)]
    roots: list[tuple[int, ...]] = [tuple(s) for s in simple]
    root_set = set(roots)
    frontier = list(simple)
    while frontier:
        new_frontier = []
        for beta in frontier:
            # Dynkin labels of beta: ⟨β,α_i∨⟩ = (Aᵀ β)_i
            cart = A.T @ beta
            for i in range(n):
                # p = max k≥0 with β - kα_i a root
                p = 0
                probe = beta.copy()
                while True:
                    probe = probe - np.eye(n, dtype=int)[i]
                    if tuple(probe) in root_set and np.all(probe >= 0):
                        p += 1
                    else:
                        break
                q = p - int(round(cart[i]))
                if q >= 1:
                    nb = beta + np.eye(n, dtype=int)[i]
                    t = tuple(nb)
                    if t not in root_set:
                        root_set.add(t)
                        new_frontier.append(nb)
        frontier = new_frontier
    return [np.array(r) for r in root_set]


@dataclass
class SimpleLie:
    kind: str
    rank: int
    name: str
    A: np.ndarray            # Cartan
    d: np.ndarray            # symmetrizers (long = 1)
    G: np.ndarray            # ½·inner-product matrix in Dynkin basis is C₂ kernel
    pos_roots: list[np.ndarray]
    h_vee: int               # dual Coxeter number (= C₂(adj))
    dim_G: int               # dimension of the algebra

    def casimir(self, labels) -> float:
        """C₂(λ) = ½·λᵀ (diag(d)A⁻¹) (λ+2ρ), λ in Dynkin labels."""
        lam = np.array(labels, dtype=float)
        rho = np.ones(self.rank)
        return 0.5 * float(lam @ self.G @ (lam + 2.0 * rho))

    def dim(self, labels) -> float:
        """Weyl dimension formula."""
        lam = np.array(labels, dtype=float)
        num = 1.0
        den = 1.0
        for alpha in self.pos_roots:
            c = alpha.astype(float)
            num *= float(np.sum(c * (lam + 1.0) * self.d))
            den *= float(np.sum(c * 1.0 * self.d))
        return num / den


def build(kind: str, rank: int, name: str) -> SimpleLie:
    A, d = _cartan(kind, rank)
    # symmetry check of the bilinear form A_{ij} d_j
    S = A * d[None, :]
    assert np.allclose(S, S.T), f"{name}: form not symmetric"
    G = np.diag(d) @ np.linalg.inv(A.T)
    pos = _positive_roots(A)
    # highest root = max height; its Dynkin labels give the adjoint Casimir
    theta = max(pos, key=lambda r: int(r.sum()))
    theta_dynkin = np.array([int(round(x)) for x in (A.T @ theta)])
    lie = SimpleLie(kind, rank, name, A, d, G, pos, 0, 0)
    h_vee = int(round(lie.casimir(theta_dynkin)))
    dim_G = 2 * len(pos) + rank
    lie.h_vee = h_vee
    lie.dim_G = dim_G
    return lie


def smallest_casimir(lie: SimpleLie) -> tuple[float, list[int]]:
    """The smallest nonzero quadratic Casimir Δ (the spectral gap) and its
    weight — the minimum over the fundamental reps ω_i."""
    best = None
    arg = None
    for i in range(lie.rank):
        labels = [0] * lie.rank
        labels[i] = 1
        c = lie.casimir(labels)
        if best is None or c < best:
            best, arg = c, labels
    return best, arg


def _dominant_weights(rank: int, max_label: int, max_total: int):
    """Enumerate dominant weights (Dynkin labels, each 0..max_label, sum
    ≤ max_total), skipping the trivial 0."""
    def rec(i, remaining):
        if i == rank:
            yield []
            return
        hi = min(max_label, remaining)
        for v in range(hi + 1):
            for rest in rec(i + 1, remaining - v):
                yield [v] + rest
    for labels in rec(0, max_total):
        if any(labels):
            yield labels


def character_Z(lie: SimpleLie, t: float, max_label: int = 6, max_total: int = 10) -> float:
    """Z_t = Σ_{λ≠0} dim(λ)²·exp(-t·C₂(λ)) over dominant weights up to a cutoff.

    The sum is dominated by the smallest-Casimir irreps (large t), so a modest
    cutoff captures it to high precision at the operating points of interest.
    """
    total = 0.0
    for labels in _dominant_weights(lie.rank, max_label, max_total):
        c2 = lie.casimir(labels)
        if t * c2 > 80.0:  # exp underflow guard; negligible contribution
            continue
        dl = lie.dim(labels)
        total += dl * dl * math.exp(-t * c2)
    return total


# The nine classical/exceptional types at small representative ranks.
def standard_zoo() -> list[SimpleLie]:
    zoo = []
    for N in (2, 3, 4, 5, 6, 7, 8):
        zoo.append(build("A", N - 1, f"A{N-1}=SU({N})"))
    for n in (2, 3, 4):
        zoo.append(build("B", n, f"B{n}=SO({2*n+1})"))
    for n in (3, 4):
        zoo.append(build("C", n, f"C{n}=Sp({n})"))
    for n in (4, 5):
        zoo.append(build("D", n, f"D{n}=SO({2*n})"))
    zoo.append(build("G", 2, "G2"))
    zoo.append(build("F", 4, "F4"))
    zoo.append(build("E", 6, "E6"))
    zoo.append(build("E", 7, "E7"))
    zoo.append(build("E", 8, "E8"))
    return zoo


if __name__ == "__main__":
    # Calibration gate: C₂(adj) must equal the textbook dual Coxeter number,
    # and dim(adjoint) must equal dim(G).
    HVEE = {  # textbook dual Coxeter numbers
        "A1=SU(2)": 2, "A2=SU(3)": 3, "A3=SU(4)": 4, "A4=SU(5)": 5,
        "A5=SU(6)": 6, "A6=SU(7)": 7, "A7=SU(8)": 8,
        "B2=SO(5)": 3, "B3=SO(7)": 5, "B4=SO(9)": 7,
        "C3=Sp(3)": 4, "C4=Sp(4)": 5,
        "D4=SO(8)": 6, "D5=SO(10)": 8,
        "G2": 4, "F4": 9, "E6": 12, "E7": 18, "E8": 30,
    }
    DIMG = {
        "A1=SU(2)": 3, "A2=SU(3)": 8, "A3=SU(4)": 15, "A4=SU(5)": 24,
        "A5=SU(6)": 35, "A6=SU(7)": 48, "A7=SU(8)": 63,
        "B2=SO(5)": 10, "B3=SO(7)": 21, "B4=SO(9)": 36,
        "C3=Sp(3)": 21, "C4=Sp(4)": 36,
        "D4=SO(8)": 28, "D5=SO(10)": 45,
        "G2": 14, "F4": 52, "E6": 78, "E7": 133, "E8": 248,
    }
    print(f"{'group':>12} {'rank':>4} {'C2(adj)=h∨':>11} {'h∨(ref)':>8} "
          f"{'dim(adj)':>9} {'dim(ref)':>8} {'Δ=C2_min':>9} {'ok':>4}")
    all_ok = True
    for lie in standard_zoo():
        delta, _ = smallest_casimir(lie)
        # adjoint dim via the highest-root Dynkin labels
        theta = max(lie.pos_roots, key=lambda r: int(r.sum()))
        theta_dyn = [int(round(x)) for x in (lie.A.T @ theta)]
        adj_dim = int(round(lie.dim(theta_dyn)))
        ok = (lie.h_vee == HVEE[lie.name]) and (adj_dim == DIMG[lie.name])
        all_ok = all_ok and ok
        print(f"{lie.name:>12} {lie.rank:>4} {lie.h_vee:>11} {HVEE[lie.name]:>8} "
              f"{adj_dim:>9} {DIMG[lie.name]:>8} {delta:>9.4f} {str(ok):>4}")
    print()
    print(f"  ALL CALIBRATION CHECKS PASS: {all_ok}")
