(() => {
  'use strict';
  const BRANCH = 'examples_dataset';
  const RAW_ROOT = `https://raw.githubusercontent.com/lemma-farm/norm-arith/${BRANCH}/`;
  const GH_ROOT = `https://github.com/lemma-farm/norm-arith/blob/${BRANCH}/`;
  const $ = (id) => document.getElementById(id);
  const state = { examples: [], category: 'All topics', query: '' };
  const esc = (value) => String(value ?? '');
  const first = (...values) => values.find((value) => value !== undefined && value !== null && value !== '');
  function normalize(raw, index) {
    const range = raw.interestingRanges?.[0] || raw.interesting_ranges?.[0] || {};
    const path = String(first(raw.exportedPath, raw.exported_path, raw.path, raw.file, raw.sourcePath, raw.source_path, raw.source?.path, '')).replace(/^\/+/, '');
    const repository = raw.repository;
    const categories = first(raw.categories, raw.features, raw.tags, []);
    const categoryList = Array.isArray(categories) ? categories : [categories];
    const category = String(first(raw.category, raw.topic, categoryList[0], raw.group, 'Other'));
    if (!categoryList.length) categoryList.push(category);
    const source = raw.source || {};
    return {
      ...raw,
      id: String(first(raw.id, raw.slug, `example-${index + 1}`)),
      title: String(first(raw.title, raw.name, raw.id, `Example ${index + 1}`)),
      description: String(first(raw.description, raw.summary, raw.abstract, raw.rationale, raw.goal, raw.genericPattern, raw.generic_pattern, 'A selected example from the Lean corpus.')),
      category,
      categories: categoryList.map(String),
      repo: String(first(raw.repo, typeof repository === 'string' ? repository : null, repository?.name, 'Examples')),
      path,
      startLine: Math.max(1, Number(first(raw.startLine, raw.start_line, range.start, source.start, raw.lineStart, raw.line_start, raw.lines?.[0], 1)) || 1),
      endLine: Math.max(1, Number(first(raw.endLine, raw.end_line, range.end, source.end, raw.lineEnd, raw.line_end, raw.lines?.[1], raw.startLine, range.start, source.start, 1)) || 1),
      provenance: String(first(raw.provenance, raw.origin, raw.sourceDescription, raw.source_description, raw.provenanceText, raw.source?.commit ? `Original source: ${source.repo || 'repository'} @ ${source.commit}, ${source.path || path}:${source.start || range.start || 1}–${source.end || range.end || 1}.` : 'Selected from the examples_dataset corpus.')),
      sourceUrl: String(first(raw.sourceUrl, raw.source_url, raw.githubUrl, raw.github_url, path ? `${GH_ROOT}${path}#L${Math.max(1, Number(first(raw.startLine, raw.start_line, range.start, source.start, 1)) || 1)}-L${Math.max(1, Number(first(raw.endLine, raw.end_line, range.end, source.end, 1)) || 1)}` : ''))
    };
  }
  function allExamples(data) {
    const values = Array.isArray(data) ? data : (data.examples || data.items || data.records || []);
    return values.map(normalize);
  }
  function topicList() {
    const topics = ['All topics', ...new Set(state.examples.flatMap((example) => example.categories).filter(Boolean))];
    const nav = $('categories'); nav.replaceChildren();
    topics.forEach((topic) => {
      const button = document.createElement('button');
      button.className = 'category' + (topic === state.category ? ' active' : ''); button.type = 'button'; button.setAttribute('aria-pressed', String(topic === state.category));
      const label = document.createElement('span'); label.textContent = topic;
      const count = document.createElement('span'); count.className = 'topic-count'; count.textContent = topic === 'All topics' ? state.examples.length : state.examples.filter((e) => e.categories.includes(topic)).length;
      button.append(label, count); button.addEventListener('click', () => { state.category = topic; topicList(); render(); }); nav.append(button);
    });
  }
  function filtered() {
    const query = state.query.trim().toLocaleLowerCase();
    const sort = $('sort').value;
    const items = state.examples.filter((e) => (state.category === 'All topics' || e.categories.includes(state.category)) && (!query || [e.title, e.description, e.category, ...e.categories, e.repo, e.path, e.provenance, e.generic_pattern, e.goal].join(' ').toLocaleLowerCase().includes(query)));
    if (sort === 'title') items.sort((a, b) => a.title.localeCompare(b.title));
    if (sort === 'repo') items.sort((a, b) => a.repo.localeCompare(b.repo) || a.title.localeCompare(b.title));
    return items;
  }
  function render() {
    const items = filtered(); const cards = $('cards'); cards.replaceChildren();
    $('count').textContent = `${state.examples.length.toLocaleString()} ${state.examples.length === 1 ? 'example' : 'examples'}`; $('status').textContent = items.length ? `${items.length.toLocaleString()} ${items.length === 1 ? 'example' : 'examples'} shown` : 'No examples match these filters.';
    items.forEach((example, index) => {
      const card = document.createElement('article'); card.className = 'card';
      const button = document.createElement('button'); button.className = 'card-main'; button.type = 'button';
      const top = document.createElement('span'); top.className = 'card-top';
      const topic = document.createElement('span'); topic.className = 'tag'; topic.textContent = example.category;
      const num = document.createElement('span'); num.className = 'card-number'; num.textContent = String(index + 1).padStart(2, '0'); top.append(topic, num);
      const title = document.createElement('span'); title.className = 'card-title'; title.textContent = example.title;
      const description = document.createElement('span'); description.className = 'card-description'; description.textContent = example.description;
      const foot = document.createElement('span'); foot.className = 'card-foot';
      const file = document.createElement('span'); file.className = 'card-file'; file.textContent = `${example.repo}${example.path ? ` / ${example.path.split('/').slice(-1)[0]}` : ''}`;
      const arrow = document.createElement('span'); arrow.className = 'card-arrow'; arrow.setAttribute('aria-hidden', 'true'); arrow.textContent = '↗'; foot.append(file, arrow);
      button.append(top, title, description, foot); button.addEventListener('click', () => openExample(example)); card.append(button); cards.append(card);
    });
  }
  function highlightLine(line) {
    const fragment = document.createDocumentFragment();
    // Keep this intentionally lightweight: source is always inserted as text, never HTML.
    const pattern = /(\b(?:theorem|lemma|example|def|abbrev|structure|inductive|where|by|namespace|end|open|import|have|show|exact|apply|intro|simp|simpa|rw|rfl|fun|let|match|with|if|then|else)\b|--.*|\b(?:Nat|Int|Real|Fin|List|Set|Prop|Type)\b)/g;
    let last = 0; let match;
    while ((match = pattern.exec(line))) {
      if (match.index > last) fragment.append(document.createTextNode(line.slice(last, match.index)));
      const span = document.createElement('span'); span.className = match[0].startsWith('--') ? 'syntax-comment' : /^[A-Z]/.test(match[0]) ? 'syntax-type' : 'syntax-keyword'; span.textContent = match[0]; fragment.append(span); last = pattern.lastIndex;
    }
    fragment.append(document.createTextNode(line.slice(last))); return fragment;
  }
  async function openExample(example) {
    const dialog = $('detail'); $('detail-title').textContent = example.title; $('detail-topic').textContent = example.category.toUpperCase(); $('detail-summary').textContent = example.description;
    $('detail-file').textContent = `${example.repo}/${example.path || '(source path unavailable)'} · lines ${example.startLine}–${example.endLine}`;
    $('detail-provenance').textContent = example.provenance;
    const validation = $('validation'); validation.replaceChildren();
    const evidence = example.validation || {};
    const facts = [];
    if (evidence.originalNativeCleanCompile === true) facts.push('Original source: clean native compile reported.');
    if (Array.isArray(evidence.originalTargetAxioms) && evidence.originalTargetAxioms.length) facts.push(`Original target axioms: ${evidence.originalTargetAxioms.join(', ')}.`);
    const build = evidence.newLayoutBuild;
    if (build) facts.push(`New layout build: ${({pending:'Pending',passed:'Passed',failed:'Failed','not-run':'Not run'})[build] || build}.`);
    if (evidence.note) facts.push(String(evidence.note));
    if (facts.length) {
      validation.hidden = false;
      const label = document.createElement('strong'); label.textContent = 'Validation evidence'; validation.append(label);
      const list = document.createElement('ul'); facts.forEach((fact) => { const item = document.createElement('li'); item.textContent = fact; list.append(item); }); validation.append(list);
    } else validation.hidden = true;
    const sourceLink = $('source-link'); sourceLink.href = example.sourceUrl || '#'; sourceLink.hidden = !example.sourceUrl;
    $('source-wrap').hidden = true; $('source-state').hidden = false; $('source-state').textContent = 'Loading source excerpt…'; $('source-code').replaceChildren();
    dialog.showModal();
    if (!example.path) { $('source-state').textContent = 'This entry does not include a source path.'; return; }
    try {
      const response = await fetch(RAW_ROOT + example.path.split('/').map(encodeURIComponent).join('/'));
      if (!response.ok) throw new Error(`Source request returned ${response.status}`);
      const lines = (await response.text()).split(/\r?\n/);
      const start = Math.min(example.startLine, lines.length); const end = Math.min(Math.max(start, example.endLine), lines.length);
      const from = Math.max(1, start - 3); const to = Math.min(lines.length, end + 3);
      const code = $('source-code');
      for (let n = from; n <= to; n++) {
        const row = document.createElement('span'); row.className = 'code-line' + (n >= start && n <= end ? ' highlighted' : ''); row.id = `line-${example.id}-${n}`;
        const number = document.createElement('span'); number.className = 'line-number'; number.textContent = n; number.setAttribute('aria-hidden', 'true');
        const text = document.createElement('span'); text.className = 'line-text'; text.append(highlightLine(lines[n - 1] ?? ''));
        row.append(number, text); code.append(row);
      }
      $('source-state').hidden = true; $('source-wrap').hidden = false;
      const target = code.querySelector('.highlighted'); if (target) target.scrollIntoView({ block: 'center' });
    } catch (error) {
      $('source-state').textContent = `Could not load this source excerpt (${error.message}). Use the GitHub link to view the file.`;
    }
  }
  $('search').addEventListener('input', (event) => { state.query = event.target.value; render(); });
  $('sort').addEventListener('change', render);
  $('clear-filters').addEventListener('click', () => { state.category = 'All topics'; state.query = ''; $('search').value = ''; topicList(); render(); });
  $('close-detail').addEventListener('click', () => $('detail').close());
  document.addEventListener('keydown', (event) => { if (event.key === '/' && !/INPUT|TEXTAREA|SELECT/.test(document.activeElement.tagName)) { event.preventDefault(); $('search').focus(); } });
  fetch('data.json').then((response) => { if (!response.ok) throw new Error(`Manifest request returned ${response.status}`); return response.json(); }).then((data) => {
    state.examples = allExamples(data); topicList(); render();
  }).catch((error) => {
    $('count').textContent = 'Collection unavailable'; $('categories').innerHTML = '<p class="muted">Topics unavailable</p>';
    $('status').textContent = `Could not load data.json (${error.message}). Ensure the dataset manifest is published beside this page.`;
  });
})();
