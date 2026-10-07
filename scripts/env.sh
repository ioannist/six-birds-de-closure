#!/usr/bin/env bash
# Source this file before running SBT-DE commands:
#   source scripts/env.sh

set -euo pipefail

export MAMBA_ROOT_PREFIX=/mnt/data-drive/sbt-de/micromamba
export CONDA_PKGS_DIRS=/mnt/data-drive/sbt-de/micromamba/pkgs
export PIP_CACHE_DIR=/mnt/data-drive/sbt-de/downloads/pip-cache
export XDG_CACHE_HOME=/mnt/data-drive/sbt-de/.cache
export TMPDIR=/mnt/data-drive/sbt-de/tmp
export MPLCONFIGDIR=/mnt/data-drive/sbt-de/.cache/matplotlib
export PYTHONNOUSERSITE=1

mkdir -p "$CONDA_PKGS_DIRS" "$PIP_CACHE_DIR" "$XDG_CACHE_HOME" "$TMPDIR" "$MPLCONFIGDIR"
export PATH="$MAMBA_ROOT_PREFIX/bin:$PATH"

eval "$("$MAMBA_ROOT_PREFIX/bin/micromamba" shell hook --shell bash)"
micromamba activate sbt-de

# Canonical env Python:
# /mnt/data-drive/sbt-de/micromamba/envs/sbt-de/bin/python
