(() => {
  'use strict';
  const BRANCH = 'examples_dataset';
  const RAW_ROOT = `https://raw.githubusercontent.com/lemma-farm/norm-arith/${BRANCH}/`;
  const GH_ROOT = `https://github.com/lemma-farm/norm-arith/blob/${BRANCH}/`;
  const $ = (id) => document.getElementById(id);
  const state = { examples: [], query: '', feature: '', activeExample: null, activeRegion: 0, sourceLines: 0, sourceByCaseId: new Map() };
  const first = (...values) => values.find((value) => value !== undefined && value !== null && value !== '');

  function normalize(raw, index) {
    const source = raw.source || {};
    const ranges = raw.interestingRegions || raw.interestingRanges || raw.interesting_ranges || [];
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
      primaryRegionId: String(first(raw.primaryRegionId, raw.primary_region_id, '')),
      regions: ranges.map((range, regionIndex) => {
        const exported = range.exported || {};
        const original = range.original || {};
        const start = Math.max(1, Number(first(exported.start, range.start, range.startLine, 1)) || 1);
        return {
          id: String(first(range.id, `region-${regionIndex + 1}`)),
          label: String(first(range.label, `Region ${regionIndex + 1}`)),
          sourceCaseIds: (Array.isArray(range.sourceCaseIds) ? range.sourceCaseIds : []).map(String),
          original,
          originalRanges: Array.isArray(range.originalRanges) ? range.originalRanges : (Object.keys(original).length ? [original] : []),
          start,
          end: Math.max(start, Number(first(exported.end, range.end, range.endLine, start)) || start)
        };
      }),
      source,
      abridged: raw.abridged || null,
      abridgedStatus: String(first(raw.abridgedStatus, '')),
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

  function lineLabel(region) {
    return region.start === region.end ? String(region.start) : `${region.start}–${region.end}`;
  }

  function focusLine(line) {
    if (!line || !state.sourceLines) return;
    const target = $(`line-${state.activeExample.id}-${line}`);
    if (!target) return;
    const targetTop = target.getBoundingClientRect().top + window.scrollY - 96;
    window.scrollTo({ top: Math.max(0, targetTop), behavior: 'smooth' });
  }

  function chooseRegion(index, scroll = true) {
    const example = state.activeExample;
    if (!example || !example.regions.length) return;
    state.activeRegion = (index + example.regions.length) % example.regions.length;
    $('region-position').textContent = `Region ${state.activeRegion + 1} of ${example.regions.length}: ${example.regions[state.activeRegion].label}`;
    $('previous-region').disabled = example.regions.length < 2;
    $('next-region').disabled = example.regions.length < 2;
    [...$('region-list').children].forEach((row, rowIndex) => row.classList.toggle('active-region', rowIndex === state.activeRegion));
    if (scroll) focusLine(example.regions[state.activeRegion].start);
  }

  function primaryRegionIndex(example) {
    const byId = example.regions.findIndex((region) => region.id === example.primaryRegionId);
    if (byId >= 0) return byId;
    const bySourceCase = example.regions.findIndex((region) => region.sourceCaseIds.includes(example.id));
    return bySourceCase >= 0 ? bySourceCase : 0;
  }

  function originalRegionHref(source) {
    if (source.url || source.sourceUrl || source.source_url) return first(source.url, source.sourceUrl, source.source_url);
    if (!source.repository || !source.commit || !source.path) return '';
    const start = first(source.start, 1); const end = first(source.end, start);
    return `https://github.com/${source.repository}/blob/${source.commit}/${source.path}#L${start}-L${end}`;
  }

  function renderRegionList(example) {
    const list = $('region-list'); list.replaceChildren();
    example.regions.forEach((region, index) => {
      const item = document.createElement('li'); item.className = 'region-item';
      const jump = document.createElement('a'); jump.className = `region-jump region-color-${index % 8}`; jump.href = `#line-${example.id}-${region.start}`;
      jump.textContent = `Region ${index + 1} · ${region.label} · lines ${lineLabel(region)}`;
      jump.addEventListener('click', (event) => { event.preventDefault(); chooseRegion(index); });
      const details = document.createElement('span'); details.className = 'region-provenance';
      const provenance = region.originalRanges.map((source) => [source.repository, source.commit, source.path,
        source.start ? `original lines ${source.start}${source.end && source.end !== source.start ? `–${source.end}` : ''}` : ''].filter(Boolean).join(' · ')).filter(Boolean).join(' ; ');
      const cases = region.sourceCaseIds.length ? `Source case IDs: ${region.sourceCaseIds.join(', ')}` : '';
      details.textContent = [provenance, cases].filter(Boolean).join(' · ') || 'Source provenance unavailable';
      item.append(jump, details);
      region.originalRanges.forEach((source, sourceIndex) => {
        const href = originalRegionHref(source);
        if (href) { const link = document.createElement('a'); link.className = 'region-source'; link.href = href; link.target = '_blank'; link.rel = 'noreferrer'; link.textContent = region.originalRanges.length > 1 ? `Open original ${sourceIndex + 1} ↗` : 'Open original ↗'; item.append(link); }
      });
      list.append(item);
    });
    if (!example.regions.length) list.innerHTML = '<li class="region-item">No interesting source regions are recorded.</li>';
    chooseRegion(primaryRegionIndex(example), false);
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

  function variantView(example, variant) {
    const a = example.abridged;
    if (variant === 'abridged' && a) {
      const start = Math.max(1, a.interestingStart || a.declarationStart || 1);
      const end = Math.max(start, a.interestingEnd || a.declarationEnd || start);
      return { ...example, variant, path: a.path,
        regions: [{ id: 'abridged-target', label: example.regions.length ? example.regions[primaryRegionIndex(example)].label : 'target', sourceCaseIds: [], original: {}, originalRanges: [], start, end }] };
    }
    return { ...example, variant: 'original' };
  }

  function setToggle(example, variant) {
    const has = Boolean(example.abridged);
    $('variant-toggle').hidden = false;
    $('variant-original').setAttribute('aria-pressed', String(variant === 'original'));
    $('variant-abridged').setAttribute('aria-pressed', String(variant === 'abridged'));
    $('variant-abridged').disabled = !has;
    $('variant-abridged').title = has ? '' : 'No abridged file: the automatic abridging did not produce a file that compiles for this example.';
    const a = example.abridged;
    $('variant-note').textContent = has
      ? `Abridged: local definitions used by the target are inlined and the directly used local theorems become hypotheses. ${a.lines.toLocaleString()} lines in one file, versus ${a.originalClosureLines.toLocaleString()} lines across ${a.originalClosureFiles} local file${a.originalClosureFiles === 1 ? '' : 's'} (this example file plus its local imports).${a.hypotheses.length ? ` Hypotheses: ${a.hypotheses.length}.` : ''}${a.axiomStubs.length ? ` Axiom stubs: ${a.axiomStubs.length}.` : ''} Interesting lines ${a.interestingStart}–${a.interestingEnd} (original file ${example.regions.length ? lineLabel(example.regions[primaryRegionIndex(example)]) : 'n/a'}).`
      : (example.abridgedStatus ? `No abridged file (${example.abridgedStatus}).` : 'No abridged file.');
  }

  async function showVariant(example, variant) {
    const view = variantView(example, variant);
    state.activeExample = view; state.activeRegion = 0; state.sourceLines = 0;
    setToggle(example, view.variant);
    const exportedRanges = view.regions.map((region) => lineLabel(region)).join(', ') || 'not specified';
    const original = example.source;
    const originalRange = view.variant === 'original' && original.start ? ` · original lines ${original.start}${original.end && original.end !== original.start ? `–${original.end}` : ''}` : '';
    $('detail-file').textContent = `${view.path || 'Source path unavailable'} · interesting file lines ${exportedRanges}${originalRange}`;
    const exportLink = $('export-link');
    exportLink.href = view.path ? `${GH_ROOT}${view.path}` : '#'; exportLink.hidden = !view.path;
    exportLink.textContent = view.variant === 'abridged' ? 'Open abridged file on GitHub ↗' : 'Open exported file on GitHub ↗';
    renderRegionList(view);
    $('source-code').replaceChildren(); $('source-wrap').hidden = true;
    $('source-state').hidden = false; $('source-state').textContent = 'Loading complete source file…';
    if (!view.path) { $('source-state').textContent = 'No exported source path is available for this entry.'; return; }
    try {
      const response = await fetch(RAW_ROOT + view.path.split('/').map(encodeURIComponent).join('/'));
      if (!response.ok) throw new Error(`Source request returned ${response.status}`);
      if (state.activeExample !== view) return;
      const sourceText = await response.text();
      const lines = sourceText.split(/\r?\n/);
      if (sourceText.endsWith('\n')) lines.pop();
      state.sourceLines = lines.length;
      const highlights = view.regions.map(({ start, end }) => [Math.min(start, lines.length), Math.min(Math.max(start, end), lines.length)]);
      const boundaries = new Map();
      view.regions.forEach((region, index) => {
        for (const [line, edge] of [[region.start, 'starts'], [region.end, 'ends']]) {
          if (!boundaries.has(line)) boundaries.set(line, []);
          boundaries.get(line).push({ index, edge, label: region.label });
        }
      });
      const code = $('source-code');
      // Render every line so the printed line numbers, source anchors, and ranges share one coordinate system.
      for (let n = 1; n <= lines.length; n++) {
        const memberships = highlights.map(([start, end], index) => n >= start && n <= end ? index : -1).filter((index) => index >= 0);
        const row = document.createElement('span'); row.className = 'code-line' + (memberships.length ? ' highlighted' : ''); row.id = `line-${view.id}-${n}`;
        const number = document.createElement('span'); number.className = 'line-number'; number.textContent = n; number.setAttribute('aria-hidden', 'true');
        const text = document.createElement('span'); text.className = 'line-text'; text.append(safeHighlight(lines[n - 1] ?? ''));
        const labels = document.createElement('span'); labels.className = 'region-boundaries';
        memberships.forEach((index) => {
          const marker = document.createElement('span'); marker.className = `region-marker region-color-${index % 8}`;
          const edges = (boundaries.get(n) || []).filter((boundary) => boundary.index === index).map((boundary) => boundary.edge);
          const edgeLabel = edges.length ? ` ${edges.join('/')}: ${view.regions[index].label}` : '';
          marker.textContent = `R${index + 1}${edgeLabel}`; labels.append(marker);
        });
        row.append(number, labels, text); code.append(row);
      }
      $('source-state').hidden = true; $('source-wrap').hidden = false;
      chooseRegion(primaryRegionIndex(view), true);
    } catch (error) {
      $('source-state').textContent = `Could not load the source file (${error.message}). Use the source links above to open it on GitHub.`;
    }
  }

  async function openExample(example) {
    state.openExample = example;
    $('list-view').hidden = true; $('detail-view').hidden = false;
    $('detail-index').textContent = `Example ${example.index} of ${state.examples.length}`;
    $('detail-title').textContent = example.title;
    $('detail-goal').textContent = example.goal;
    $('detail-features').textContent = example.features.length ? `Features: ${example.features.join(', ')}` : '';
    const original = example.source;
    const originalLink = $('original-link');
    originalLink.href = example.sourceUrl || '#'; originalLink.hidden = !example.sourceUrl;
    const origin = [original.repository, original.commit, original.path].filter(Boolean).join(' · ');
    $('detail-provenance').textContent = origin ? `Original source: ${origin}` : '';
    window.scrollTo({ top: 0, behavior: 'instant' });
    await showVariant(example, 'original');
  }

  $('search-form').addEventListener('submit', (event) => event.preventDefault());
  $('search').addEventListener('input', (event) => { state.query = event.target.value; render(); });
  $('feature-filter').addEventListener('change', (event) => { state.feature = event.target.value; render(); });
  $('previous-region').addEventListener('click', () => chooseRegion(state.activeRegion - 1));
  $('next-region').addEventListener('click', () => chooseRegion(state.activeRegion + 1));
  $('variant-original').addEventListener('click', () => state.openExample && showVariant(state.openExample, 'original'));
  $('variant-abridged').addEventListener('click', () => state.openExample && state.openExample.abridged && showVariant(state.openExample, 'abridged'));
  $('back').addEventListener('click', () => { $('detail-view').hidden = true; $('list-view').hidden = false; window.scrollTo({ top: 0, behavior: 'instant' }); });
  fetch('data.json').then((response) => { if (!response.ok) throw new Error(`Manifest request returned ${response.status}`); return response.json(); }).then((data) => {
    const rows = Array.isArray(data) ? data : (data.examples || []);
    state.examples = rows.map(normalize);
    state.sourceByCaseId = new Map(state.examples.map((example) => [example.id, example.source]));
    state.examples.forEach((example) => example.regions.forEach((region) => {
      if (!region.originalRanges.length) {
        region.originalRanges = region.sourceCaseIds.map((id) => state.sourceByCaseId.get(id)).filter(Boolean);
        if (!region.originalRanges.length && region.sourceCaseIds.includes(example.id) && Object.keys(example.source).length) region.originalRanges = [example.source];
      }
    }));
    const features = [...new Set(state.examples.flatMap((example) => example.features))].filter(Boolean).sort();
    features.forEach((feature) => { const option = document.createElement('option'); option.value = feature; option.textContent = feature; $('feature-filter').append(option); });
    render();
  }).catch((error) => { $('status').textContent = `Could not load the dataset (${error.message}).`; });
})();
