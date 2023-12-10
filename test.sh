#!/usr/bin/env bash
set -euxo pipefail

${LAKE:-lake} build Partax.Test
find tests -type f | xargs -n1 ${LAKE:-lake} env lean
echo "all done"
