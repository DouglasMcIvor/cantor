#!/usr/bin/env bash
# Drop into an interactive bash shell inside the running cantor-dev container.
set -euo pipefail

docker compose up -d

# Forward the calling terminal's color-capability signal — `docker compose
# exec` does not inherit the host shell's environment, so without this the
# container sees TERM unset/dumb and tools fall back to no/reduced color.
#
# CARGO_HOME is overridden from the image default (/usr/local/cargo, which
# lives on the container's read-only root filesystem — see docker-compose.yml's
# `read_only: true`) to the bind-mounted ${HOST_HOME}/.cargo instead, so cargo
# can actually write its registry/git caches. This container mirrors host
# paths (see docker-compose.yml's volume comments), so the host's own $HOME
# is the same path the container mounts read-write.
#
# TZ is forwarded (rather than bind-mounting /etc/localtime) because
# /etc/localtime is itself a symlink on most hosts: bind-mounting it onto the
# container's own /etc/localtime symlink writes through to the resolved
# target (e.g. .../zoneinfo/Etc/UTC), silently corrupting that zoneinfo file
# while leaving the symlink's name unchanged — glibc then computes correct
# UTC offsets from the clobbered file, but Node/ICU still reports the zone as
# "UTC" because it reads the zone ID from the symlink name, not the file
# contents. Setting TZ avoids all of this; every timezone-aware library
# checks it before consulting /etc/localtime.
exec docker compose exec \
  -e "TERM=${TERM:-xterm-256color}" \
  -e "COLORTERM=${COLORTERM:-}" \
  -e "CARGO_HOME=${HOME}/.cargo" \
  -e "TZ=${TZ:-$(cat /etc/timezone 2>/dev/null || echo UTC)}" \
  cantor-dev bash
