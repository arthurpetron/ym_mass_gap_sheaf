# Running the continuum campaign on Google Cloud Batch

The continuum-limit study for `m(0++)/sqrt(sigma)` vs the Teper benchmark needs
several `(beta, L)` points, each a `glueball` + `string_tension` measurement.
The points are independent, so instead of running them sequentially on one
machine (days) we run each on its own multi-core VM **concurrently** via
**Google Cloud Batch** (wall time = the single slowest point).

The crate is dependency-free, so the only cloud artifacts are a tiny container
image and a parameter table. Only the heavy MCMC runs in-cloud; the Python
analysis + continuum fit is done locally afterward on the pulled JSONs.

## Files

| File | Purpose |
|---|---|
| `Dockerfile` | Multi-stage build of the `glueball` + `string_tension` binaries |
| `cloudbuild.yaml` | Build the image with Cloud Build (no local Docker needed) |
| `points.tsv` | One row per `(beta, L)` point; row index = Batch task index |
| `entrypoint.sh` | Maps `BATCH_TASK_INDEX` -> a `points.tsv` row and runs it |
| `batch-job.json` | Batch job: Tier A (rows 0-3) as a 4-task array |

## One-time setup

Pick a project and region, and set shell variables (adjust to yours). Use
**hyphens, not underscores**, in resource names — Artifact Registry and GCS
reject or dislike underscores, so do NOT name a resource after this repo's
folder (`ym_mass_gap_sheaf`):

```bash
PROJECT=$(gcloud config get-value project)   # e.g. ym-gap
REGION=us-central1
REPO=ym-sim                   # Artifact Registry repo name -- hyphens only
BUCKET=${PROJECT}-ym-runs     # GCS bucket for outputs (globally unique, hyphens)
IMAGE=${REGION}-docker.pkg.dev/${PROJECT}/${REPO}/ym-sim:latest
```

Authenticate (run these yourself in the session with the `!` prefix, e.g.
`! gcloud auth login` — they open a browser):

```
! gcloud auth login
! gcloud auth application-default login
```

Enable APIs and create the registry + bucket:

```bash
gcloud services enable batch.googleapis.com compute.googleapis.com \
    artifactregistry.googleapis.com cloudbuild.googleapis.com \
    logging.googleapis.com storage.googleapis.com

gcloud artifacts repositories create "$REPO" \
    --repository-format=docker --location="$REGION" \
    --description="YM SU(2) lattice engine" || true

gsutil mb -l "$REGION" "gs://${BUCKET}" || true
```

**Verify the registry exists before building** — Cloud Build pushes to it but
will NOT create it, and a missing repo fails the push with
`name unknown: Repository "..." not found`:

```bash
gcloud artifacts repositories describe "$REPO" --location="$REGION"
```

If that errors, the create above did not succeed (often a stray underscore in
`$REPO`, or the API was not enabled yet) — fix `$REPO` and re-run the create.

## Build the image (Cloud Build, from the repo root)

```bash
# from the repository root, NOT from cloud/
gcloud builds submit --config cloud/cloudbuild.yaml \
    --substitutions=_IMAGE="${IMAGE}" .
```

This compiles the Rust binaries in the cloud and pushes `ym-sim:latest` to
Artifact Registry. Takes a couple of minutes.

## How the points are tuned

`points.tsv` is not arbitrary — each column is set from the measured SU(2)
physics so the continuum extrapolation is clean and not dominated by avoidable
systematics:

- **`L` (matched physical volume).** Held so `L*sqrt(sigma)*a ~ 4.3-4.5` across
  all beta, using the known `sqrt(sigma)*a` (0.369, 0.266, 0.222, 0.186, 0.157,
  0.133 for beta = 2.3 .. 2.6; our beta=2.5/2.6 runs confirm 0.180/0.128). This
  keeps the **torelon-to-glueball mass ratio ~ 1.18-1.24** at every point, so the
  winding torelon stays safely above the 0++ and does not contaminate the scalar
  plateau. (Letting `L` lag — e.g. L30 at beta=2.6 — drops that ratio to ~1.11,
  torelon and glueball nearly degenerate.)
- **`rmax = L/2`.** The largest Wilson loop the box allows; the previous smaller
  `rmax` left the Cornell fit `V(r)=V0+sigma*r-c/r` with only 4-5 points and a
  10-40% error on sigma. More points in the linear regime is the single biggest
  lever on string-tension precision, which is the binding error here.
- **`rmin`.** Set so `rmin*sqrt(sigma)*a ~ 0.6-0.8` (the short-distance Coulomb
  term subdominant) while leaving enough of the `[rmin, rmax]` window for the fit.
- **`g_meas` (glueball statistics) scales with beta.** Finer lattices resolve the
  0++ plateau only at larger tau, where signal/noise is worse, so the config
  count grows from 60k (beta=2.3) to 300k (beta=2.6).
- **`s_meas` (string-tension statistics).** Boosted to 40k-100k configs (was
  ~6k): sigma was the noisy observable and would otherwise dominate the
  continuum-fit uncertainty.
- **`g_therm` / `s_therm`.** Grow with beta for critical slowing down (mitigated
  by the overrelaxation, dynamical exponent ~ 1).
- **`seed`.** Distinct per point -> independent samples.

## Cost tiers (decide how far in beta to go)

Cost scales like `L^4 x meas`, so the high-beta points dominate. Run in two tiers:

| row | point | ~VM-hours (incl. string tension) |
|---|---|---|
| 0 | 2.30 / L12 | ~0.25 |
| 1 | 2.40 / L16 | ~1.4 |
| 2 | 2.45 / L20 | ~4.5 |
| 3 | 2.50 / L24 | ~11 |
| 4 | 2.55 / L28 | ~25 |
| 5 | 2.60 / L32 | ~55 |

- **Tier A (rows 0-3, `batch-job.json` as shipped):** a 4-point continuum fit
  spanning `sigma*a^2 = 0.136 -> 0.035`. ~17 VM-h total, wall ~11 h (the L24
  point), **~$25 on-demand** on `c2d-standard-32`. Validates the pipeline and
  already gives a real `a -> 0` extrapolation.
- **Tier B (rows 4-5):** the scaling-tail points that tighten the continuum value
  toward a 6-sigma statement. These dominate — **~80 VM-h, ~$100-200**, wall set
  by the L32 point (~1 day on `c2d-standard-60`). Run each as its own job on a
  bigger machine (below), or on Spot.

Start with Tier A. Inspect the 4-point fit before paying for the tail.

## Grant the Batch service account access (one-time — easy to miss)

Batch tasks run as the Compute Engine default service account. On newer projects
this SA no longer has the broad Editor role, so it starts with **none** of the
permissions Batch needs and you must grant all four explicitly. Skipping these
fails in confusing ways:

| role | without it |
|---|---|
| `logging.logWriter` | **no logs appear at all** (even for a running, failing task) |
| `storage.objectAdmin` | task exits 1 — the JSON `--out` write to the GCS mount is denied |
| `artifactregistry.reader` | image pull fails, container never starts |
| `batch.agentReporter` | task-status reporting fails |

```bash
PNUM=$(gcloud projects describe "$PROJECT" --format='value(projectNumber)')
SA="${PNUM}-compute@developer.gserviceaccount.com"

for role in logging.logWriter storage.objectAdmin artifactregistry.reader batch.agentReporter; do
  gcloud projects add-iam-policy-binding "$PROJECT" \
      --member="serviceAccount:${SA}" --role="roles/${role}" --condition=None
done

# confirm all four:
gcloud projects get-iam-policy "$PROJECT" --flatten="bindings[].members" \
    --filter="bindings.members:${SA}" --format="value(bindings.role)" | sort
```

If a running task fails with `exit code 1` and **no container logs**, this grant
(specifically `logging.logWriter` + `storage.objectAdmin`) is almost always why.

## CPU quota (the first thing that bites a new project)

New projects often cap `CPUS_ALL_REGIONS` (global vCPUs) at **32**, and have a
low regional `C2D_CPUS`. Tier A as shipped wants 4 x 32 = 128 vCPUs at once, so
it fails immediately with `CODE_GCE_QUOTA_EXCEEDED` (state -> FAILED, not stuck).
Two responses:

- **Raise the quota (the real fix).** Console: IAM & Admin -> Quotas -> filter
  "CPUs (all regions)" -> 256, and "C2D CPUs" in your region -> 128. Usually
  approved in minutes to hours. Then submit `batch-job.json` (the 128-vCPU
  parallel version) normally.
- **Fit inside 32 vCPUs now.** Submit `batch-job-32vcpu.json` instead:
  `parallelism: 2` x `c2d-standard-16` = 32 vCPUs, two points at a time on 16
  cores each (and `c2d-standard-16` is more widely available than `-32`, dodging
  the transient `ZONE_RESOURCE_POOL_EXHAUSTED` you may also see). The L24 point
  is slow on 16 cores (~20 h); set `taskCount: 3` to run just L12/L16/L20 now and
  do L24 after the quota bump.

## Submit the campaign (Tier A: beta = 2.3, 2.4, 2.45, 2.5)

Fill the placeholders in `batch-job.json` and submit a 4-task array (one VM per
beta point, all concurrent):

```bash
sed -e "s|IMAGE_URI|${IMAGE}|" -e "s|BUCKET_NAME|${BUCKET}|" \
    cloud/batch-job.json > /tmp/ym-batch.json

gcloud batch jobs submit ym-continuum-1 \
    --location="$REGION" --config=/tmp/ym-batch.json
```

Monitor:

```bash
gcloud batch jobs describe ym-continuum-1 --location="$REGION"
gcloud batch tasks list  --job=ym-continuum-1 --location="$REGION" \
    --task-group=group0
# live logs:
gcloud logging read 'labels."batch.googleapis.com/job_id"="ym-continuum-1"' \
    --limit=50 --freshness=2h
```

## Pull results and analyze locally

When the job state is `SUCCEEDED`:

```bash
gsutil -m cp "gs://${BUCKET}/runs/*.json" visualizations/pilot/su2/

# then the usual local pipeline (per point):
.venv/bin/python -m computations.long_runs.glueball_analysis \
    visualizations/pilot/su2/glueball-L16-b2.40.json --plot ...-b2.40.svg
.venv/bin/python -m computations.long_runs.string_tension_analysis \
    visualizations/pilot/su2/sigma-L16-b2.40.json --rmin 3 --plot ...
# and the continuum extrapolation:
.venv/bin/python -m computations.long_runs.continuum_trend   # point it at the new JSONs
```

## The heavy points (Tier B: beta = 2.55/L28, 2.60/L32 — rows 4-5)

These dominate the cost (`L^4`), so don't let them hold up Tier A. Two ways to
run them on a bigger machine:

- **Simplest — one job, all rows, big machine.** Submit the array with
  `taskCount: 6` and `machineType: c2d-standard-60`: the small points finish in
  minutes and release their VMs while L28/L32 keep running. You pay per VM for
  only what each uses.
- **Per-point control.** Bake a one-row `points.tsv` (just the heavy point) into
  a second image tag and submit a `taskCount: 1` job on `c2d-standard-60` with
  `maxRunDuration: 172800s` (48 h). Use this if you want different machine sizes
  or Spot settings per point.

### Cheaper: Spot VMs (~60-70% off)

Set `"provisioningModel": "SPOT"` in `batch-job.json`. Caveat: the engine has
**no checkpointing**, so a preempted multi-hour run restarts from scratch
(Batch retries the task). Fine for the short low-beta points; risky for L28/L32,
where a preemption late in the run wastes hours. Use Spot for rows 0-3, on-demand
for the heavy points. (Adding checkpointing to the engine would remove this
caveat and is the right move before a large Spot campaign.)

## First-run smoke test

Before the full campaign, shrink `points.tsv` to `g_meas=20000 s_meas=4000` and
submit — it finishes in minutes and verifies the image, the GCS mount, and the
JSON shapes end-to-end for a few dollars.
