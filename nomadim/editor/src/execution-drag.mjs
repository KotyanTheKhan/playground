import { laneX, rowY, laneFromX, rowFromY, isInDeleteZone } from './execution-svg.mjs';

const SVGNS = 'http://www.w3.org/2000/svg';

// Classify the grabbed element into a gesture descriptor.
export function classifyTarget(el) {
  if (!el || !el.closest) return { kind: null };
  const conn = el.closest('[data-sync]');
  if (conn) return { kind: 'connector', sync: parseInt(conn.getAttribute('data-sync'), 10) };
  const label = el.closest('.proc-label');
  if (label) return { kind: 'header', proc: parseInt(label.getAttribute('data-proc'), 10) };
  const lane = el.closest('.lane-hit');
  if (lane) return { kind: 'lane', proc: parseInt(lane.getAttribute('data-proc'), 10) };
  return { kind: null };
}

// Attach drag editing to a freshly rendered swimlane <svg>. `handlers` =
// { onNewSync(a,b), onReorderProcess(from,to), onMoveSync(from,to), onDeleteSync(i) }.
// Window-level move/up listeners are added on pointerdown and removed on pointerup,
// so nothing leaks across re-renders (each render produces a new <svg>).
export function attachDrag(svgEl, execution, handlers) {
  const n = execution.n_procs;
  const nSyncs = execution.syncs.length;
  const deleteZone = svgEl.querySelector('.delete-zone');
  let drag = null;

  const toSvg = (ev) => {
    const pt = svgEl.createSVGPoint();
    pt.x = ev.clientX; pt.y = ev.clientY;
    return pt.matrixTransform(svgEl.getScreenCTM().inverse());
  };
  const clearHot = () => svgEl.querySelectorAll('.hot').forEach((e) => e.classList.remove('hot'));
  const hot = (sel) => { clearHot(); const e = svgEl.querySelector(sel); if (e) e.classList.add('hot'); };
  function clearFeedback() {
    svgEl.querySelectorAll('.drag-overlay').forEach((e) => e.remove());
    clearHot();
    if (deleteZone) deleteZone.classList.remove('active', 'hot');
  }
  function rubberBand(x1, y1, x2, y2) {
    let ln = svgEl.querySelector('line.drag-overlay');
    if (!ln) { ln = document.createElementNS(SVGNS, 'line'); ln.setAttribute('class', 'drag-overlay'); svgEl.appendChild(ln); }
    ln.setAttribute('x1', x1); ln.setAttribute('y1', y1);
    ln.setAttribute('x2', x2); ln.setAttribute('y2', y2);
  }

  function onMove(ev) {
    if (!drag) return;
    ev.preventDefault();
    const p = toSvg(ev);
    if (drag.kind === 'lane') {
      rubberBand(laneX(drag.proc), rowY(-1), p.x, p.y);
      const t = laneFromX(p.x, n);
      if (t >= 0) hot(`.lane-hit[data-proc="${t}"]`); else clearHot();
    } else if (drag.kind === 'header') {
      const t = laneFromX(p.x, n);
      if (t >= 0) hot(`.lane-hit[data-proc="${t}"]`); else clearHot();
    } else if (drag.kind === 'connector') {
      if (deleteZone) deleteZone.classList.add('active');
      if (isInDeleteZone(p.y, execution)) {
        clearHot();
        if (deleteZone) deleteZone.classList.add('hot');
      } else {
        if (deleteZone) deleteZone.classList.remove('hot');
        const to = rowFromY(p.y, nSyncs);
        if (to >= 0) hot(`.sync[data-sync="${to}"]`); else clearHot();
      }
    }
  }

  function onUp(ev) {
    if (!drag) return;
    const p = toSvg(ev);
    const d = drag;
    drag = null;
    window.removeEventListener('pointermove', onMove);
    window.removeEventListener('pointerup', onUp);
    clearFeedback();
    if (d.kind === 'lane') {
      const t = laneFromX(p.x, n);
      if (t >= 0 && t !== d.proc) handlers.onNewSync(d.proc, t);
    } else if (d.kind === 'header') {
      const t = laneFromX(p.x, n);
      if (t >= 0 && t !== d.proc) handlers.onReorderProcess(d.proc, t);
    } else if (d.kind === 'connector') {
      if (isInDeleteZone(p.y, execution)) handlers.onDeleteSync(d.sync);
      else {
        const to = rowFromY(p.y, nSyncs);
        if (to >= 0 && to !== d.sync) handlers.onMoveSync(d.sync, to);
      }
    }
  }

  function onDown(ev) {
    const c = classifyTarget(ev.target);
    if (!c.kind) return;
    ev.preventDefault();
    drag = c;
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  svgEl.addEventListener('pointerdown', onDown);
}
