import { executionSvg } from './execution-svg.mjs';

// Render the execution as a swimlane SVG into `container` (replacing its content).
export function renderExecution(container, execution) {
  container.innerHTML = executionSvg(execution);
}

export function clearExecution(container) {
  container.innerHTML = '';
}
