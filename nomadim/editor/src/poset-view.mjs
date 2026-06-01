import { posetToElements } from './cytoscape-elements.mjs';

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
      { selector: 'edge', style: {
        'width': 2, 'line-color': '#888', 'target-arrow-color': '#888',
        'target-arrow-shape': 'triangle', 'curve-style': 'bezier',
      } },
    ],
  });
  return cy;
}

// Replace the rendered graph with the given poset and re-run the layout.
export function renderPoset(cy, poset) {
  cy.elements().remove();
  cy.add(posetToElements(poset));
  cy.layout({ name: 'dagre', rankDir: 'BT', nodeSep: 30, rankSep: 50 }).run();
  cy.fit(undefined, 30);
}
