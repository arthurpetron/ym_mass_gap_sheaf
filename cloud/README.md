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
| `batch-job.json` | Batch job: the affordable set (rows 0-3) as a 4-task array |

## One-time setup

Pick a project and region, and set shell variables (adjust to yours):

```bash
PROJECT=$(gcloud config get-value project)
REGION=us-central1
REPO=ym                       # Artifact Registry repo name
BUCKET=${PROJECT}-ym-runs     # GCS bucket for outputs (must be globally unique)
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

## Build the image (Cloud Build, from the repo root)

```bash
# from the repository root, NOT from cloud/
gcloud builds submit --config cloud/cloudbuild.yaml \
    --substitutions=_IMAGE="${IMAGE}" .
```

This compiles the Rust binaries in the cloud and pushes `ym-sim:latest` to
Artifact Registry. Takes a couple of minutes.

## Submit the campaign (the affordable set: beta = 2.3, 2.4, 2.45, 2.5)

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

## The heavy points (beta = 2.55/L26, 2.60/L30 — rows 4-5)

Cost scales like `L^4`, so these dominate. Run each as its OWN job on a bigger
machine rather than holding up the array. Example for the L30 point (row 5):

```bash
# a single-task job that selects row 5 via taskCount/parallelism on a 60-vCPU VM
# (copy batch-job.json -> batch-heavy.json, set taskCount=1, machineType
#  c2d-standard-60, maxRunDuration 86400s, and add to the taskSpec.environment:
#    "BATCH_TASK_INDEX_OFFSET" is NOT a thing -- instead duplicate the row you
#    want as row 0 of a points-heavy.tsv baked into a second image tag, OR just
#    submit the affordable job with taskCount=6 and a c2d-standard-60 machine
#    and let the small points finish fast while the big ones run.)
```

Simplest: submit **one** job with `taskCount: 6` (all rows) on
`c2d-standard-60`; the small points finish in minutes and release their VMs
while L26/L30 keep running. You pay only for what each VM uses.

## Cost and wall-time (rough, us-central1, on-demand)

`c2d-standard-32` ~ $1.4/h; `c2d-standard-60` ~ $2.6/h. With `g_meas=600000`:

| point | ~VM-hours (c2d-32) |
|---|---|
| 2.3/L12 | ~0.4 |
| 2.4/L16 | ~1.2 |
| 2.45/L18 | ~1.8 |
| 2.5/L22 | ~4 |
| 2.55/L26 | ~8 (use c2d-60: ~4) |
| 2.6/L30 | ~14 (use c2d-60: ~7) |

Affordable set (rows 0-3, concurrent): **~$10-15, wall time ~4 h.**
Full 6-point campaign: **~$40-60 on-demand**, wall time set by the L30 point.

### Cheaper: Spot VMs (~60-70% off)

Set `"provisioningModel": "SPOT"` in `batch-job.json`. Caveat: the engine has
**no checkpointing**, so a preempted multi-hour run restarts from scratch
(Batch retries the task). Fine for the short low-beta points; risky for L26/L30,
where a preemption late in the run wastes hours. Use Spot for rows 0-3, on-demand
for the heavy points. (Adding checkpointing to the engine would remove this
caveat and is the right move before a large Spot campaign.)

## First-run smoke test

Before the full campaign, shrink `points.tsv` to `g_meas=20000 s_meas=4000` and
submit — it finishes in minutes and verifies the image, the GCS mount, and the
JSON shapes end-to-end for a few dollars.
