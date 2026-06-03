# Running the continuum campaign on Google Cloud Batch

The continuum-limit study for `m(0++)/sqrt(sigma)` vs the Teper benchmark needs
several `(beta, L)` points, each a glueball **and** a string-tension
measurement. Two design choices make this fast and cheap:

- **One chain, both observables.** The `measure` binary runs a single
  heatbath+overrelax chain and measures the 0++/2++ glueball correlators *and*
  the Wilson-loop grid on every config — instead of two independent chains. One
  thermalization, ~30% fewer sweeps.
- **Shard each point across machines.** A point is split into `shards`
  independent chains (distinct seeds), one Batch task each, run concurrently on
  **Spot** VMs. Independent draws merge into one larger jackknife ensemble, so
  wall time ≈ (point cost) / shards and the heavy points stop blowing the
  per-task time cap. The local `merge_shards.py` concatenates the per-shard
  bins afterward.
- **Checkpoint to GCS.** Every shard writes a resumable checkpoint to the
  GCS-mounted output dir every few minutes (and rewrites its partial JSONs, so a
  run is analyzable live). A preempted Spot VM **resumes** instead of restarting
  — which is what makes Spot safe even for the multi-hour points.

The crate is dependency-free; the only cloud artifacts are a tiny container
image and a parameter table. Only the heavy MCMC runs in-cloud; the Python
analysis + continuum fit is done locally on the merged JSONs.

## Files

| File | Purpose |
|---|---|
| `Dockerfile` | Multi-stage build of the `measure` (+ `glueball`, `string_tension`) binaries |
| `cloudbuild.yaml` | Build the image with Cloud Build (no local Docker needed) |
| `points.tsv` | One row per `(beta, L)` point: physics knobs + `shards` |
| `entrypoint.sh` | Maps `(POINT_ROW, BATCH_TASK_INDEX)` -> a point + shard and runs `measure` with checkpointing |
| `batch-job.json` | Templated Batch job (Spot, shard array); placeholders filled by `launch.sh` |
| `launch.sh` | Submit one Batch job per point (rendering the template) |
| `merge_all.sh` | Pull shard JSONs from GCS and merge each point (calls `merge_shards.py`) |

The merge tool itself is `computations/long_runs/merge_shards.py`.

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

`points.tsv` columns are set from the measured SU(2) physics so the continuum
extrapolation is clean and not dominated by avoidable systematics:

- **`L` (matched physical volume).** Held so `L*sqrt(sigma)*a ~ 4.3-4.5` across
  all beta, keeping the torelon safely above the 0++ so it does not contaminate
  the scalar plateau.
- **`rmax = L/2`** (and `tmax = rmax`). The largest Wilson loop the box allows;
  more points in the linear regime of `V(r)=V0+sigma*r-c/r` is the single
  biggest lever on string-tension precision, which is the binding error here.
- **`meas` (chain length) scales with beta.** Finer lattices resolve the 0++
  plateau only at larger tau, so the total config target grows with beta. Both
  observables now share this one chain.
- **`sigma_smear`.** APE steps on the spatial links for the Wilson loops
  (captured for free from the glueball smear ladder).
- **`bins`** are *per shard*; the merge concatenates them, so the final ensemble
  has `bins * shards` jackknife bins.
- **`seed_base`.** Shard `k` uses `seed_base + k`; rows are spaced by ≥ shards so
  seeds never collide across points -> all shards are independent draws.
- **`shards`.** How many concurrent machines the point is split across. Heavy
  points get more shards so each shard finishes in a similar wall time.

## Cost / sharding (decide how far in beta to go)

Per-point compute scales like `L^4 x meas`; sharding divides the **wall** time
(not the cost) by `shards`. Approximate single-machine (16-vCPU) cost and the
resulting per-shard wall time at the shipped `shards`:

| row | point | ~VM-h (point) | shards | ~wall/shard |
|---|---|---|---|---|
| 1 | 2.30 / L12 | ~0.3 | 4  | minutes |
| 2 | 2.40 / L16 | ~1.5 | 4  | ~0.4 h |
| 3 | 2.45 / L20 | ~5   | 6  | ~0.8 h |
| 4 | 2.50 / L24 | ~12  | 8  | ~1.5 h |
| 5 | 2.55 / L28 | ~28  | 12 | ~2.3 h |
| 6 | 2.60 / L32 | ~60  | 20 | ~3 h |

On Spot (~60-70% off) the whole 6-point campaign is on the order of ~$40-70 of
compute, and — quota permitting (below) — completes in a few wall hours rather
than days. Tune `shards` after a real benchmark; these are starting points.

## Grant the Batch service account access (one-time — easy to miss)

Batch tasks run as the Compute Engine default service account. On newer projects
this SA no longer has the broad Editor role, so grant all four roles explicitly:

| role | without it |
|---|---|
| `logging.logWriter` | **no logs appear at all** (even for a running, failing task) |
| `storage.objectAdmin` | task exits 1 — the JSON/checkpoint write to the GCS mount is denied |
| `artifactregistry.reader` | image pull fails, container never starts |
| `batch.agentReporter` | task-status reporting fails |

```bash
PNUM=$(gcloud projects describe "$PROJECT" --format='value(projectNumber)')
SA="${PNUM}-compute@developer.gserviceaccount.com"

for role in logging.logWriter storage.objectAdmin artifactregistry.reader batch.agentReporter; do
  gcloud projects add-iam-policy-binding "$PROJECT" \
      --member="serviceAccount:${SA}" --role="roles/${role}" --condition=None
done
```

If a running task fails with `exit code 1` and **no container logs**, this grant
(specifically `logging.logWriter` + `storage.objectAdmin`) is almost always why.

## Spot CPU quota (the lever that decides wall time)

Sharding only buys concurrency if the quota allows the shards to run at once.
`N` concurrent shards need `N * vCPU(MACHINE)` **Spot** vCPUs in the region
(quota `PREEMPTIBLE_CPUS`, plus the global `CPUS_ALL_REGIONS`). New projects
often cap these low (e.g. 32), which would run only 2 × 16-vCPU shards at a time.

- **Raise the quota (the real fix).** Console: IAM & Admin -> Quotas -> filter
  "Preemptible CPUs" (your region) and "CPUs (all regions)" -> request enough for
  your peak (e.g. 256). Usually approved in minutes to hours.
- **Cap it for now.** `launch.sh` respects `MAX_PARALLEL` and `MACHINE`: set
  `MAX_PARALLEL=2` (shards queue, running 2 at a time) and/or a smaller
  `MACHINE` to fit more shards per vCPU. Checkpointing makes a long-queued shard
  harmless — it just runs later.

## Submit the campaign

`launch.sh` renders `batch-job.json` per point and submits one Spot job each:

```bash
export PROJECT REGION BUCKET REPO          # from setup above
cloud/launch.sh                # all points (rows 1..6)
cloud/launch.sh 1 2 3 4        # just the lighter points first
cloud/launch.sh 6             # only L32

# knobs:
MACHINE=c2d-standard-8 MAX_PARALLEL=4 cloud/launch.sh 5 6
```

Each job is named `ym-c-l<L>-b<beta>` (e.g. `ym-c-l24-b25`). Monitor:

```bash
gcloud batch jobs list --location="$REGION"
gcloud batch tasks list --job=ym-c-l24-b25 --location="$REGION" --task_group=group0
# live logs (and progress: the binary prints "[progress] collected N configs"):
gcloud logging read 'labels."batch.googleapis.com/job_id"="ym-c-l24-b25"' \
    --limit=50 --freshness=2h
```

Because each shard rewrites its partial `glueball-*-s*.json` / `sigma-*-s*.json`
at every checkpoint, you can also just `merge_all.sh` mid-run to see how the
point is converging so far.

> Note: the GCS volume mounts at `/mnt/disks/out` (set in `OUT_DIR` and the job's
> `mountPath`). The Batch VM runs Container-Optimized OS with a read-only root, so
> the mount point must live under a writable path like `/mnt/disks/` — a plain
> `/mnt/out` fails gcsfuse with `stat /mnt/out: no such file or directory`.

## Pull, merge, and analyze locally

`merge_all.sh` pulls every `*-s*.json` shard from GCS and merges each point into
the single `glueball-L<L>-b<beta>.json` / `sigma-...` the analysis expects:

```bash
cloud/merge_all.sh                       # -> visualizations/pilot/su2/
# (or a custom dest dir: cloud/merge_all.sh /tmp/runs)

# then the usual local pipeline (per point), unchanged:
.venv/bin/python -m computations.long_runs.glueball_analysis \
    visualizations/pilot/su2/glueball-L24-b2.50.json --plot ...-b2.50.svg
.venv/bin/python -m computations.long_runs.string_tension_analysis \
    visualizations/pilot/su2/sigma-L24-b2.50.json --rmin 4 --plot ...
.venv/bin/python -m computations.long_runs.continuum_trend   # point it at the merged JSONs
```

The merged JSON carries `n_shards`, `shard_seeds`, and `total_cpu_seconds` for
provenance; the analysis ignores the extra keys.

## First-run smoke test

Before the full campaign, shrink `points.tsv` (e.g. `meas=20000`, `shards=2`) and
`launch.sh 1` — it finishes in minutes and verifies the image, the GCS mount,
checkpoint/resume, and the shard→merge→analysis path end-to-end for a few cents.
