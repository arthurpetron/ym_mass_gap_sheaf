# Exact cutoff-one five-cycle Haar moment balance

The constructive Lean route now identifies the two remaining signed moments
with fivefold Haar integrals over the based cycles

```text
[0, 4, 5, 6, 10].
```

At cutoff one, the exact whole-slab Haar contraction reduces independently to
the 128 closed assignments in a rank-seven binary face-cycle space.  Reading
the unique vacuum row from the zero-signature Kraus block and summing all 128
assignments gives, in the Lean heat coordinate `w`,

```text
R(w) = Haar_5(row)
     = 1 + 4 w^18,

C(w) = Haar_5(constant)
     = 1 + 32 w^18 + 96 w^30 + 224 w^36 + 192 w^42 + 3 w^48.
```

Thus

```text
C(w) - R(w)
  = 28 w^18 + 96 w^30 + 224 w^36 + 192 w^42 + 3 w^48,
```

which is strictly positive for `w > 0`.

## Centered normalization

Let `p = R/C` be the normalized physical vacuum marginal.  Both centered
expressions share the exact numerator

```text
N(w) = C(w) - R(w)^2
     = 24 w^18 + 96 w^30 + 208 w^36 + 192 w^42 + 3 w^48.
```

The unnormalized signed-Haar side and normalized physical side are therefore

```text
signed centered moment   = N/C,
physical centered moment = N/C^2.
```

Their exact difference is

```text
((C - 1) N) / C^2,
```

with numerator

```text
768 w^36 + 5376 w^48 + 12032 w^54 + 19968 w^60
+ 41640 w^66 + 83456 w^72 + 83520 w^78 + 38160 w^84
+ 1152 w^90 + 9 w^96.
```

Every displayed coefficient is positive.  Hence the proposed centered
same-action balance fails strictly for every `w > 0`; it holds only at the
degenerate point `w = 0`.

## Certificate boundary

The exact rational evaluation and algebra are executable in
`computations/cutoff_one_haar5_moment_balance.py`.  The route from the two
moments to `Haar_5` is already theorem-checked in
`BF4ExactCutoffOneTransmittedDegree.lean`.  The remaining formalization task is
to import the 128-surface polynomial certificate into Lean, so the displayed
closed forms and strict obstruction become kernel-checked theorems rather
than executable exact certificates.
