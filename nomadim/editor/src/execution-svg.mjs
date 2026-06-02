// Pure renderer + geometry for the execution swimlane. executionSvg returns a
// complete <svg> string (no DOM access). Geometry helpers are exported so the
// drag controller hit-tests against the exact same coordinate system.

const MARGIN = 40;     // left/top padding
const LANE_GAP = 90;   // horizontal gap between process lanes
const ROW_GAP = 50;    // vertical gap between sync rows
const TOP = 30;        // y of the first sync row baseline

export function laneX(p) { return MARGIN + p * LANE_GAP; }
export function rowY(i) { return TOP + (i + 1) * ROW_GAP; }
export function svgWidth(execution) { return MARGIN * 2 + Math.max(0, execution.n_procs - 1) * LANE_GAP; }
export function svgHeight(execution) { return TOP + (execution.syncs.length + 1) * ROW_GAP + MARGIN; }

// Nearest process lane for an SVG-space x, clamped to [0, n-1]; -1 if no lanes.
export function laneFromX(x, n) {
  if (n <= 0) return -1;
  return Math.max(0, Math.min(n - 1, Math.round((x - MARGIN) / LANE_GAP)));
}

// Nearest sync-row slot for an SVG-space y, clamped to [0, nSyncs-1]; -1 if none.
export function rowFromY(y, nSyncs) {
  if (nSyncs <= 0) return -1;
  return Math.max(0, Math.min(nSyncs - 1, Math.round((y - TOP) / ROW_GAP) - 1));
}

// True if an SVG-space y is within the bottom delete-zone band.
export function isInDeleteZone(y, execution) {
  return y > svgHeight(execution) - MARGIN;
}

export function executionSvg(execution) {
  const n = execution.n_procs;
  const syncs = execution.syncs;
  const width = svgWidth(execution);
  const height = svgHeight(execution);

  const parts = [];
  parts.push(`<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" class="exec-svg" data-procs="${n}" data-syncs="${syncs.length}">`);

  // Per lane: a transparent wide hit-rect (easy to grab + hit-test), the visible
  // lane line, and a grabbable process-header label.
  for (let p = 0; p < n; p++) {
    const x = laneX(p);
    parts.push(`<rect class="lane-hit" data-proc="${p}" x="${x - LANE_GAP / 2}" y="${TOP}" width="${LANE_GAP}" height="${height - MARGIN - TOP}" fill="transparent" />`);
    parts.push(`<line class="lane" x1="${x}" y1="${TOP}" x2="${x}" y2="${height - MARGIN}" />`);
    parts.push(`<text class="proc-label" data-proc="${p}" x="${x}" y="${TOP - 10}" text-anchor="middle">P${p}</text>`);
  }

  // Sync connectors (ordered top->bottom) + endpoint dots (also data-sync so the
  // dots are grabbable) + index labels.
  syncs.forEach(([a, b], i) => {
    const y = rowY(i);
    const xa = laneX(a), xb = laneX(b);
    parts.push(`<line class="sync" x1="${xa}" y1="${y}" x2="${xb}" y2="${y}" data-sync="${i}" data-a="${a}" data-b="${b}" />`);
    parts.push(`<circle class="event" data-sync="${i}" cx="${xa}" cy="${y}" r="5" />`);
    parts.push(`<circle class="event" data-sync="${i}" cx="${xb}" cy="${y}" r="5" />`);
    parts.push(`<text class="sync-label" x="${Math.min(xa, xb) - 12}" y="${y + 4}" text-anchor="end">${i}</text>`);
  });

  // Delete zone (hidden until a connector drag activates it).
  parts.push(`<g class="delete-zone"><rect x="4" y="${height - MARGIN + 4}" width="${Math.max(0, width - 8)}" height="${MARGIN - 8}" rx="4" /><text x="${width / 2}" y="${height - MARGIN / 2 + 4}" text-anchor="middle">drop here to delete</text></g>`);

  parts.push(`</svg>`);
  return parts.join('');
}
