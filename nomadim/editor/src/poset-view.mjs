import { posetToElements, criticalPairsToElements } from './cytoscape-elements.mjs';

// Initialise a Cytoscape instance in `container` for poset rendering. Uses the
// dagre layered layout bottom-to-top so minimal elements sit at the bottom and
// cover edges point upward (the Hasse convention). Returns the cy instance.
export function initPosetView(container) {
  // cytoscape + cytoscape-dagre are loaded as globals by index.html script tags.
  const cy = window.cytoscape({
    container,
    elements: [],
    style: [
      { selector: 'node', style: {
        'background-color': '#4f8cff', 'label': 'data(label)',
        'color': '#fff', 'text-valign': 'center', 'text-halign': 'center',
        'width': 28, 'height': 28, 'font-size': 12,
      } },
      { selector: 'node:selected', style: {
        'background-color': '#ff7043', 'border-width': 3, 'border-color': '#b53',
      } },
      { selector: 'edge', style: {
        'width': 2, 'line-color': '#888', 'target-arrow-color': '#888',
        'target-arrow-shape': 'triangle', 'curve-style': 'bezier',
      } },
      { selector: 'edge:selected', style: { 'line-color': '#ff7043', 'width': 4 } },
      { selector: 'edge.critical', style: {
        'width': 2, 'line-color': '#e0457b', 'line-style': 'dashed',
        'target-arrow-shape': 'none', 'curve-style': 'unbundled-bezier',
        'control-point-distances': 40, 'opacity': 0.8,
      } },
    ],
  });
  return cy;
}

// Replace the rendered graph with the given poset and re-run the layout.
// (Critical overlay, if any, must be re-applied by the caller after this.)
export function renderPoset(cy, poset) {
  cy.elements().remove();
  cy.add(posetToElements(poset));
  cy.layout({ name: 'dagre', rankDir: 'BT', nodeSep: 30, rankSep: 50 }).run();
  cy.fit(undefined, 30);
}

// Add critical-pair overlay edges on top of the current layout (no relayout, so
// the Hasse positions are preserved). Clears any prior overlay first.
export function setCriticalOverlay(cy, pairs) {
  cy.remove('edge.critical');
  cy.add(criticalPairsToElements(pairs));
}

export function clearCriticalOverlay(cy) {
  cy.remove('edge.critical');
}
