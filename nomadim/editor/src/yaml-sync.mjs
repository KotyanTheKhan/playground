import { loadFromDocument } from './model.mjs';

// Serialize the current model back to YAML text (poset takes precedence if both
// are present, matching what the viewer renders).
export function modelToYaml(client, model) {
  if (model.poset) return client.dumpPoset(model.poset);
  if (model.execution) return client.dumpExecution(model.execution);
  return '';
}

// Parse YAML text into a model. Throws (via the client) on malformed input;
// callers should catch and surface the error.
export function yamlToModel(client, text) {
  return loadFromDocument(client.parseDocument(text));
}
