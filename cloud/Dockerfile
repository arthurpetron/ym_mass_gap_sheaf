# SU(2) lattice engine for the continuum campaign on Google Cloud Batch.
# The crate is std-only (no deps), so the build is fast and the runtime image
# is tiny.  Only the heavy compute (JSON-producing MCMC) runs in-cloud; the
# Python analysis + plotting is done locally after pulling the JSONs back.
#
# Build context is the REPO ROOT (so simulations/ and cloud/ are both visible):
#   gcloud builds submit --config cloud/cloudbuild.yaml \
#       --substitutions=_IMAGE=REGION-docker.pkg.dev/PROJECT/ym/ym-sim:latest .

# ---- build stage ----
FROM rust:1-slim AS build
WORKDIR /src
COPY simulations/ ./simulations/
# `measure` is the combined, checkpointing, shardable driver used by the
# campaign; glueball/string_tension stay for ad-hoc single-observable runs.
RUN cd simulations && cargo build --release \
    --bin measure --bin glueball --bin string_tension

# ---- runtime stage ----
FROM debian:stable-slim
COPY --from=build /src/simulations/target/release/measure        /usr/local/bin/measure
COPY --from=build /src/simulations/target/release/glueball       /usr/local/bin/glueball
COPY --from=build /src/simulations/target/release/string_tension /usr/local/bin/string_tension
COPY cloud/entrypoint.sh /usr/local/bin/entrypoint.sh
COPY cloud/points.tsv    /work/points.tsv
RUN chmod +x /usr/local/bin/entrypoint.sh
ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
