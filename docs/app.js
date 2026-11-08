(() => {
  'use strict';
  const BRANCH = 'examples_dataset';
  const RAW_ROOT = `https://raw.githubusercontent.com/lemma-farm/norm-arith/${BRANCH}/`;
  const GH_ROOT = `https://github.com/lemma-farm/norm-arith/blob/${BRANCH}/`;
  const $ = (id) => document.getElementById(id);
  const state = { examples: [], query: '', feature: '' };
  const first = (...values) => values.find((value) => value !== undefined && value !== null && value !== '');

  function normalize(raw, index) {
    const source = raw.source || {};
    const ranges = raw.interestingRanges || raw.interesting_ranges || [];
    const path = String(first(raw.exportedPath, raw.exported_path, raw.path, raw.file, source.path, '')).replace(/^\/+/, '');
    const features = first(raw.features, raw.categories, raw.tags, []);
    return {
      ...raw,
      id: String(first(raw.id, raw.slug, `example-${index + 1}`)),
      title: String(first(raw.title, raw.name, raw.id, `Example ${index + 1}`)),
      path,
      goal: String(first(raw.goal, raw.rationale, raw.description, raw.summary, '')),
      pattern: String(first(raw.generic_pattern, raw.genericPattern, '')),
      features: (Array.isArray(features) ? features : [features]).map(String),
      ranges: ranges.map((range) => ({ start: Math.max(1, Number(range.start) || 1), end: Math.max(1, Number(range.end) || Number(range.start) || 1) })),
      source,
      sourceUrl: String(first(raw.sourceUrl, raw.source_url, source.source_url, '')),
      index: index + 1
    };
  }

  function searchable(example) {
    return [example.title, example.goal, example.pattern, example.path, ...example.features,
      example.source.repository, example.source.commit, example.source.path, example.sourceUrl].join(' ').toLocaleLowerCase();
  }

  function render() {
    const query = state.query.trim().toLocaleLowerCase();
    const items = state.examples.filter((example) =>
      (!state.feature || example.features.includes(state.feature)) && (!query || searchable(example).includes(query)));
    const list = $('examples'); list.replaceChildren();
    $('count').textContent = state.examples.length.toLocaleString();
    $('status').textContent = `${items.length.toLocaleString()} of ${state.examples.length.toLocaleString()} examples`;
    items.forEach((example) => {
      const row = document.createElement('li');
      const button = document.createElement('button'); button.type = 'button'; button.className = 'example-row';
      const title = document.createElement('span'); title.className = 'example-title'; title.textContent = example.title;
      const meta = document.createElement('span'); meta.className = 'example-meta'; meta.textContent = [example.features.join(', '), example.path].filter(Boolean).join(' · ');
      const goal = document.createElement('span'); goal.className = 'example-goal'; goal.textContent = example.goal || example.pattern;
      button.append(title, meta, goal); button.addEventListener('click', () => openExample(example)); row.append(button); list.append(row);
    });
  }

  function rangesLabel(ranges) {
    return ranges.length ? ranges.map((range) => range.start === range.end ? String(range.start) : `${range.start}–${range.end}`).join(', ') : 'not specified';
  }

  function safeHighlight(line) {
    const fragment = document.createDocumentFragment();
    const pattern = /(\b(?:theorem|lemma|example|def|abbrev|structure|inductive|where|by|namespace|end|open|import|have|show|exact|apply|intro|simp|simpa|rw|rfl|fun|let|match|with|if|then|else)\b|--.*|\b(?:Nat|Int|Real|Fin|List|Set|Prop|Type)\b)/g;
    let last = 0; let match;
    while ((match = pattern.exec(line))) {
      if (match.index > last) fragment.append(document.createTextNode(line.slice(last, match.index)));
      const token = document.createElement('span');
      token.className = match[0].startsWith('--') ? 'syntax-comment' : /^[A-Z]/.test(match[0]) ? 'syntax-type' : 'syntax-keyword';
      token.textContent = match[0]; fragment.append(token); last = pattern.lastIndex;
    }
    fragment.append(document.createTextNode(line.slice(last)));
    return fragment;
  }

  async function openExample(example) {
    $('list-view').hidden = true; $('detail-view').hidden = false;
    $('detail-index').textContent = `Example ${example.index} of ${state.examples.length}`;
    $('detail-title').textContent = example.title;
    $('detail-goal').textContent = example.goal;
    $('detail-features').textContent = example.features.length ? `Features: ${example.features.join(', ')}` : '';
    const original = example.source;
    const exportedRanges = rangesLabel(example.ranges);
    const originalRange = original.start ? ` · original lines ${original.start}${original.end && original.end !== original.start ? `–${original.end}` : ''}` : '';
    $('detail-file').textContent = `${example.path || 'Source path unavailable'} · interesting file lines ${exportedRanges}${originalRange}`;
    const exportLink = $('export-link');
    exportLink.href = example.path ? `${GH_ROOT}${example.path}` : '#'; exportLink.hidden = !example.path;
    const originalLink = $('original-link');
    originalLink.href = example.sourceUrl || '#'; originalLink.hidden = !example.sourceUrl;
    const origin = [original.repository, original.commit, original.path].filter(Boolean).join(' · ');
    $('detail-provenance').textContent = origin ? `Original source: ${origin}` : '';
    $('source-code').replaceChildren(); $('source-wrap').hidden = true;
    $('source-state').hidden = false; $('source-state').textContent = 'Loading complete source file…';
    window.scrollTo({ top: 0, behavior: 'instant' });
    if (!example.path) { $('source-state').textContent = 'No exported source path is available for this entry.'; return; }
    try {
      const response = await fetch(RAW_ROOT + example.path.split('/').map(encodeURIComponent).join('/'));
      if (!response.ok) throw new Error(`Source request returned ${response.status}`);
      const lines = (await response.text()).split(/\r?\n/);
      const highlights = example.ranges.map(({ start, end }) => [Math.min(start, lines.length), Math.min(Math.max(start, end), lines.length)]);
      const firstHighlighted = highlights[0]?.[0] || null;
      const code = $('source-code');
      // Render every line so the printed line numbers, source anchors, and ranges share one coordinate system.
      for (let n = 1; n <= lines.length; n++) {
        const isHighlighted = highlights.some(([start, end]) => n >= start && n <= end);
        const row = document.createElement('span'); row.className = 'code-line' + (isHighlighted ? ' highlighted' : ''); row.id = `line-${example.id}-${n}`;
        const number = document.createElement('span'); number.className = 'line-number'; number.textContent = n; number.setAttribute('aria-hidden', 'true');
        const text = document.createElement('span'); text.className = 'line-text'; text.append(safeHighlight(lines[n - 1] ?? ''));
        row.append(number, text); code.append(row);
      }
      $('source-state').hidden = true; $('source-wrap').hidden = false;
      if (firstHighlighted) {
        const target = $(`line-${example.id}-${firstHighlighted}`);
        const targetTop = target.getBoundingClientRect().top + window.scrollY - 96;
        window.scrollTo({ top: Math.max(0, targetTop), behavior: 'smooth' });
      }
    } catch (error) {
      $('source-state').textContent = `Could not load the source file (${error.message}). Use the source links above to open it on GitHub.`;
    }
  }

  $('search-form').addEventListener('submit', (event) => event.preventDefault());
  $('search').addEventListener('input', (event) => { state.query = event.target.value; render(); });
  $('feature-filter').addEventListener('change', (event) => { state.feature = event.target.value; render(); });
  $('back').addEventListener('click', () => { $('detail-view').hidden = true; $('list-view').hidden = false; window.scrollTo({ top: 0, behavior: 'instant' }); });
  fetch('data.json').then((response) => { if (!response.ok) throw new Error(`Manifest request returned ${response.status}`); return response.json(); }).then((data) => {
    const rows = Array.isArray(data) ? data : (data.examples || []);
    state.examples = rows.map(normalize);
    const features = [...new Set(state.examples.flatMap((example) => example.features))].filter(Boolean).sort();
    features.forEach((feature) => { const option = document.createElement('option'); option.value = feature; option.textContent = feature; $('feature-filter').append(option); });
    render();
  }).catch((error) => { $('status').textContent = `Could not load the dataset (${error.message}).`; });
})();
