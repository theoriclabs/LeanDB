# A LeanDB base as a container: build the base's executable, ship only it.
#
#   docker build --build-arg BASE=tickets -t leandb-tickets .
#   docker run -p 7411:7411 -v tickets-data:/data -e LEANDB_TOKEN=s3cret leandb-tickets
#
# dashboard requires the untracked sibling repo ../../../leandb-http (see
# RELEASING.md); the other examples build standalone. The instance lives in
# the /data volume (LEANDB_DB); the server binds 0.0.0.0 inside the
# container, so set LEANDB_TOKEN (or pass --auth-token) before publishing
# the port. Named volumes are chown'd to the `leandb` user (created in the
# runtime stage); bind mounts (-v ./data:/data) must be writable by that
# uid, or serve dies at startup with a bare SQLite error.

FROM ubuntu:24.04 AS build
ARG BASE=tickets
# BASE reaches RUN/COPY paths, so validate it before use: only example
# directory names are allowed (no injection, no ../.. traversal).
RUN case "${BASE}" in ''|*[!a-z0-9_]*) echo "invalid BASE: '${BASE}'" >&2; exit 1;; esac \
    && test -d "examples/${BASE}" || { echo "unknown BASE: '${BASE}' (no examples/${BASE} directory)" >&2; exit 1; }
ENV DEBIAN_FRONTEND=noninteractive
RUN apt-get update && apt-get install -y --no-install-recommends \
      curl git ca-certificates build-essential \
    && rm -rf /var/lib/apt/lists/*
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
ENV PATH=/root/.elan/bin:$PATH
WORKDIR /src
# the engine (a path dependency of every example) and the examples
COPY lean-toolchain lakefile.toml lake-manifest.json LeanDb.lean Main.lean ./
COPY LeanDb ./LeanDb
COPY examples ./examples
RUN cd examples/${BASE} && lake build ${BASE}

FROM ubuntu:24.04
ARG BASE=tickets
RUN apt-get update && apt-get install -y --no-install-recommends ca-certificates libgmp10 curl tzdata \
    && rm -rf /var/lib/apt/lists/* \
    && useradd --system --create-home --shell /usr/sbin/nologin leandb
COPY --from=build /src/examples/${BASE}/.lake/build/bin/${BASE} /usr/local/bin/base
RUN mkdir -p /data && chown leandb:leandb /data
USER leandb
VOLUME /data
ENV LEANDB_DB=/data/base.sqlite
EXPOSE 7411
HEALTHCHECK --interval=30s --timeout=3s --start-period=30s CMD curl -sf http://127.0.0.1:7411/healthz || exit 1
ENTRYPOINT ["/usr/local/bin/base"]
CMD ["serve", "--http", "7411", "--bind", "0.0.0.0"]
