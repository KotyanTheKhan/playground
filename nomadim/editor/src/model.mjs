// In-memory document model. Holds at most one poset and/or one execution (as
// returned by the WASM parseDocument). For the 2b-i viewer the model is loaded
// from a document and queried; structural editing arrives in 2b-ii.

export function emptyModel() {
  return { poset: null, execution: null, meta: null };
}

// doc: parseDocument output { execution?, poset?, meta? }
export function loadFromDocument(doc) {
  return { poset: doc.poset ?? null, execution: doc.execution ?? null, meta: doc.meta ?? null };
}

export function getMeta(model) {
  return model.meta ?? {};
}

// Immutable note update (preserves other meta fields).
export function setNotes(model, notes) {
  return { ...model, meta: { ...(model.meta ?? {}), notes } };
}

// Adjacency (array-of-arrays) of the current poset, or null if none.
export function posetAdjacency(model) {
  return model.poset ? model.poset.edges : null;
}

// True if the model has something renderable as a poset.
export function hasPoset(model) {
  return model.poset != null;
}
