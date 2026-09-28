# Reproducible environment for `make verify`.
#   docker build -t perfectpower . && docker run --rm perfectpower
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
        ca-certificates curl git make python3 && rm -rf /var/lib/apt/lists/*
RUN curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
        | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"
WORKDIR /work
COPY . .
# Toolchain from lean-toolchain; Mathlib from lake-manifest.json.  Falls back to building
# Mathlib from source (about 1900 modules) when the build cache is unreachable.
RUN lake exe cache get || true
CMD ["make", "verify"]
