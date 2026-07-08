# A2 via binary forms: the apolar-norm-ratio 6j VALUE + the real Zreal recoupling discharge

Date: 2026-07-08. Build: `lake build` exit 0 (776 jobs). Frontier guard: **OK, 5 types
uninhabited** (unchanged — nothing reacted to close a Clay frontier). Axiom gate on every
new declaration: ⊆ {propext, Quot.sound}. No `native_decide`/`sorry`/`admit`/`Prop := True`.

New files (MAIN tree, LEAN-CORE only, imported in `YMGap.lean`):
- `lean/YMGap/Continuum/A2ApolarValue.lean`
- `lean/YMGap/Continuum/A2RecouplingDischarge.lean`

Untouched (owned by boundedH agent): SelfAdjointHamiltonian / BoundedHamiltonianFiniteVol /
HaddDischarge / AsymptoticSpectralLoc.

---

## STEP 1 — the 6j VALUE from the rep category (apolar norm ratio), NOT the shape witness

The dim-weighted Racah kernel `P = dim(e)dim(f){6j}² = 1/4` at the smallest SU(2)
tetrahedron is computed as a **ratio of apolar norms** of the transvectant Clebsch–Gordan
coupling trees, entirely from `TransvectantCG.apolarHalf`:

- `eps i j := apolarHalf (mono i) (mono j)` — the ε-form on spin ½ DEFINED from the top
  transvectant (`eps_values`: (0,1)=−1,(1,0)=1,(0,0)=(1,1)=0). Loop `tr(ε·εᵀ) = −2`
  (`apolarLoop_eq`).
- Two coupling-tree intertwiners `treeA`,`treeB` (couple (12)→e→(·3) vs (23)→f→(1·)) as
  ε-contractions; invariant apolar net pairing `netPair` (all 4 legs ε-capped).
- **Apolar norms** (kernel-checked from apolarHalf): `⟨A,A⟩ = ⟨B,B⟩ = 12`, `⟨A,B⟩ = −6`
  (`normAA_eq`, `normBB_eq`, `crossAB_eq`), overlap genuinely nonzero (`crossAB_ne_zero`).
- **THE VALUE (`apolar_dimweighted_6j_sq`, axiom-free `decide`):**
  `⟨A,B⟩² ≃ (1/4)·⟨A,A⟩·⟨B,B⟩` — division-free form of `P = ⟨A,B⟩²/(⟨A,A⟩⟨B,B⟩) = 36/144 = 1/4`.
  This is the genuine 6j value from binary-forms invariant theory, **not** the constant
  `1/4` shape witness.
- **Matches the physical kernel** (`sixj_value_is_apolar_norm_ratio`, `decide`):
  `racahKernelQ(smallestTetra)·⟨A,A⟩·⟨B,B⟩ ≃ ⟨A,B⟩²` — the factorial Racah 6j² and the
  apolar-norm 6j² agree exactly (two independent routes to `1/4`).
- **PentagonNumericCore INHABITED from the rep category** (`racahApolarCore`): kernel =
  the label-varying faithful `racahKernelQ` (matches `racahKernel6` at every label — NOT
  constant); its value certified as the apolar ratio. `racahApolarCore_fractional`
  (`1/4 ∉ {0,1}`), `racahApolarCore_not_perm` (defeats every permutation surrogate).

Cross-checked numerically before formalizing: the unitary recoupling coefficient
`U = ⟨A|B⟩/√(⟨A|A⟩⟨B|B⟩) = −1/2`, `U² = 1/4`, matching Wigner `{½½1;½½1} = 1/6`,
`3·3·(1/6)² = 1/4`.

## STEP 2 — the REAL Zreal from the coherent recoupling family (not Zreal := Ξ)

`PhysicalRecouplingInterface` (the genuine minimal A2 interface from `RecouplingInterface`)
is INHABITED NON-VACUOUSLY (`physRecouplingInterface`):
- `Zreal := TreePartitionIdentity.ZrealTree` — the real partition function built by the
  iterated single-link Haar collapse (one `Z2_collapse`/2-fold-orthogonality per shared
  link = the elementary recoupling), **defined by its own recursion WITHOUT any reference
  to Ξ** (so NOT the `under_cut_is_fake` trap `Zreal := Ξ`). `physInterface_Zreal_is_real`
  exhibits its genuine Haar-collapse cons-recursion.
- `identity := tree_partition_identity` — the PROVED `Ξ ≃ ZrealTree` for **every** Γ.
- `recoupling := elementaryRecoupling` — the discharged, trace-faithful (3≠1) Jones–Wenzl
  datum (`physInterface_recoupling_nonvacuous`), carrying the apolar 6j value
  (`interface_sixj_value_is_apolar`).

## STEP 3 — what A2 discharges vs what remains

**DISCHARGED (genuine, axiom-clean, non-vacuous):** the literal A2 consumer
`Stage1Loopy.physical_identity` — which invokes ONLY the `identity` field
(`RecouplingInterface.physical_identity_factors`) — is supplied at `w4` with a REAL,
non-Ξ-alias `Zreal`: `physical_identity_discharged : (Xi w4 Γ label).eqv
((physRecouplingInterface w4 label).Zreal Γ)`. Plus: the elementary recoupling (proved
inhabited), the coherence (`pentagon_from_uniqueness`, pre-existing), and the 6j VALUE
(Step 1, from the apolar rep category).

**REMAINS (sharply named, NOT faked, uninhabited — the genuine loopy gap):** `ZrealTree`
is the true Haar partition function only on TREE geometry (≤2 shared links). On the loopy
`z4` lattice (links shared by ≥3 plaquettes) the TRUE Wilson/Haar `Zreal` needs the
closed-fusion-loop 6j **RECOUPLING IDENTITY** `SixJRecoupling.biedenharn_elliott` (the full
Racah sum rule ∀ a,b,c,d,e — strictly stronger than the single smallest-tetrahedron VALUE
computed here). The residual is exactly: *build the loopy `Zreal` weaving the 6j identity
into the partition function, and prove `Ξ ≃` that loopy `Zreal`.* `SixJRecoupling` stays
uninhabited; frontier guard stays 5.

## HONEST VERDICT

A2 is **REDUCED, not fully CLOSED — a genuine, honest advance, not a D-move to closure.**
The 6j VALUE is now computed from binary-forms invariant theory as a real apolar-norm ratio
(cross-validated against the factorial kernel), the coherence is proved, the elementary
recoupling is discharged, and the literal consumer identity `Ξ ≃ Zreal` is discharged with
a REAL (non-Ξ) tree-level Haar-collapse `Zreal`. The single sharp remaining atom is the
**loopy ≥3-shared-link 6j-network Zreal matching** (the full `biedenharn_elliott` identity
woven into the loopy partition function, and `Ξ ≃` it) — the R1/6j wall. Value + coherence
+ real tree-Zreal are the cheap genuine-physics parts, now done; the loopy 6j identity is
the residual. Clay YM mass gap stays OPEN. Nothing faked; guard unchanged.
