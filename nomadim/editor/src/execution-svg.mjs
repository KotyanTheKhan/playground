// Pure renderer: turn an execution { n_procs, syncs } into an SVG string showing
// process swimlanes (vertical lanes) and ordered synchronization connectors
// (horizontal, with an event dot on each endpoint lane). Returns a complete
// <svg> element string. No DOM access — unit-testable.

const MARGIN = 40;     // left/top padding
const LANE_GAP = 90;   // horizontal gap between process lanes
const ROW_GAP = 50;    // vertical gap between sync rows
const TOP = 30;        // y of the first sync row baseline

export function executionSvg(execution) {
  const n = execution.n_procs;
  const syncs = execution.syncs;
  const width = MARGIN * 2 + Math.max(0, n - 1) * LANE_GAP;
  const height = TOP + (syncs.length + 1) * ROW_GAP + MARGIN;
  const laneX = (p) => MARGIN + p * LANE_GAP;
  const rowY = (i) => TOP + (i + 1) * ROW_GAP;

  const parts = [];
  parts.push(`<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" class="exec-svg" data-procs="${n}" data-syncs="${syncs.length}">`);

  // Lanes + process labels.
  for (let p = 0; p < n; p++) {
    const x = laneX(p);
    parts.push(`<line class="lane" x1="${x}" y1="${TOP}" x2="${x}" y2="${height - MARGIN}" />`);
    parts.push(`<text class="proc-label" x="${x}" y="${TOP - 10}" text-anchor="middle">P${p}</text>`);
  }

  // Sync connectors (in order, top to bottom) + endpoint dots + index labels.
  syncs.forEach(([a, b], i) => {
    const y = rowY(i);
    const xa = laneX(a), xb = laneX(b);
    parts.push(`<line class="sync" x1="${xa}" y1="${y}" x2="${xb}" y2="${y}" data-sync="${i}" data-a="${a}" data-b="${b}" />`);
    parts.push(`<circle class="event" cx="${xa}" cy="${y}" r="5" />`);
    parts.push(`<circle class="event" cx="${xb}" cy="${y}" r="5" />`);
    parts.push(`<text class="sync-label" x="${Math.min(xa, xb) - 12}" y="${y + 4}" text-anchor="end">${i}</text>`);
  });

  parts.push(`</svg>`);
  return parts.join('');
}
