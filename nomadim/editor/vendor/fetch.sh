#!/usr/bin/env bash
# Download the pinned browser (UMD) builds of the graph libraries into this dir.
# These files are committed so the editor works offline and reproducibly.
set -euo pipefail
cd "$(dirname "$0")"
curl -fsSL -o cytoscape.min.js       https://unpkg.com/cytoscape@3.30.2/dist/cytoscape.min.js
curl -fsSL -o dagre.min.js           https://unpkg.com/dagre@0.8.5/dist/dagre.min.js
curl -fsSL -o cytoscape-dagre.js     https://unpkg.com/cytoscape-dagre@2.5.0/cytoscape-dagre.js
echo "✅ vendored cytoscape 3.30.2, dagre 0.8.5, cytoscape-dagre 2.5.0"
