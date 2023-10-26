#!/usr/bin/env bash
set -euxo pipefail

${LAKE:-lake} build Partax.Test
find tests -type f -exec ${LAKE:-lake} env lean {} \;
echo "all done"
