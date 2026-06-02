// Save `text` to a file. Uses the File System Access API when available
// (Chromium, secure context — localhost qualifies); otherwise falls back to a
// browser download. Returns 'saved' (picker) or 'downloaded' (fallback).
export async function saveText(text, suggestedName = 'poset.yaml') {
  if (typeof window !== 'undefined' && window.showSaveFilePicker) {
    const handle = await window.showSaveFilePicker({
      suggestedName,
      types: [{ description: 'YAML', accept: { 'text/yaml': ['.yaml', '.yml'] } }],
    });
    const writable = await handle.createWritable();
    await writable.write(text);
    await writable.close();
    return 'saved';
  }
  const blob = new Blob([text], { type: 'text/yaml' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = suggestedName;
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(url);
  return 'downloaded';
}
