// Thin typed wrapper over the Embind module. `factory` is the MODULARIZE export
// (createNomadim): in the browser it's window.createNomadim, in Node it's
// require('../public/nomadim.js'). All marshalling of JSON lives here so the
// rest of the app works with plain JS objects/arrays.
export async function makeClient(factory) {
  const m = await factory();
  return {
    isDim2: (adjacency) => m.isDim2(JSON.stringify(adjacency)),
    findRealizer: (adjacency) => JSON.parse(m.findRealizer(JSON.stringify(adjacency))),
    criticalPairs: (adjacency) => JSON.parse(m.criticalPairs(JSON.stringify(adjacency))),
    dimension: (adjacency, caps) => JSON.parse(m.dimension(JSON.stringify(adjacency), caps ? JSON.stringify(caps) : '')),
    findOneRealizer: (adjacency, caps) => JSON.parse(m.findOneRealizer(JSON.stringify(adjacency), caps ? JSON.stringify(caps) : '')),
    allRealizers: (adjacency, caps) => JSON.parse(m.allRealizers(JSON.stringify(adjacency), caps ? JSON.stringify(caps) : '')),
    expandExecution: (execution) => JSON.parse(m.expandExecution(JSON.stringify(execution))),
    parseDocument: (yamlText) => JSON.parse(m.parseDocument(yamlText)),
    dumpPoset: (poset) => m.dumpPoset(JSON.stringify(poset)),
    dumpExecution: (execution) => m.dumpExecution(JSON.stringify(execution)),
    dumpDocument: (doc) => m.dumpDocument(JSON.stringify(doc)),
    version: () => m.version(),
  };
}
