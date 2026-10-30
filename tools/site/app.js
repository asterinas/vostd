/* VOSTD verification dashboard.
 *
 * Renders stats/snapshot.json (current per-module verification status) and
 * stats/history.json (totals per recorded commit) as charts + tables. Chart
 * colors resolve from CSS custom properties so the whole page follows the
 * media-query palette; charts re-init on color-scheme change.
 * Names from JSON enter DOM via textContent or an escaper, never innerHTML. */

"use strict";

const SERIES = [
  { key: "verified_exec", name: "Verified", cssVar: "--series-verified" },
  { key: "trusted", name: "Trusted boundary", cssVar: "--series-trusted" },
  { key: "spec", name: "Spec", cssVar: "--series-spec" },
  { key: "proof", name: "Proof", cssVar: "--series-proof" },
  { key: "verified_apis", name: "Verified APIs", cssVar: "--series-api" },
];

const TM_STATUS = [
  // Status palette follows code_treemap.py; identical in light/dark themes.
  { key: "verified_exec", name: "Fully verified", cssVar: "--tm-verified", darkText: true },
  { key: "trusted", name: "Trusted boundary", cssVar: "--tm-trusted", darkText: true },
  { key: "unverified", name: "Unverified", cssVar: "--tm-unverified", darkText: true },
  { key: "unplanned", name: "Unplanned", cssVar: "--tm-unplanned", darkText: false },
];

const css = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
const esc = (s) =>
  String(s).replace(/[&<>"']/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]),
  );
const fmt = (n) => new Intl.NumberFormat("en", { notation: "compact" }).format(n);
const fmtFull = (n) => new Intl.NumberFormat("en").format(n);
const PCT = (n) => `${(100 * n).toFixed(1)}%`;

function baseText() {
  return {
    ink: css("--ink"),
    ink2: css("--ink-2"),
    ink3: css("--ink-3"),
    grid: css("--grid"),
    baseline: css("--baseline"),
    surface: css("--surface-1"),
    good: css("--good-text"),
    bad: css("--bad-text"),
  };
}

/* ---------------------------------------------------------------- tiles */

function renderTiles(snapshot, historyPoints) {
  const totals = snapshot.totals;
  const current = historyPoints.length ? historyPoints[historyPoints.length - 1] : null;
  const previous =
    historyPoints.length > 1 ? historyPoints[historyPoints.length - 2] : null;

  const specs = [
    { label: "Total executable LoC", value: totals.total, deltaKey: null },
    {
      label: "Verified",
      value: totals.verified_exec,
      deltaKey: "verified_exec",
      upIsGood: true,
    },
    {
      label: "Trusted boundary",
      value: totals.trusted,
      deltaKey: "trusted",
      upIsGood: false,
    },
    {
      label: "Verified APIs",
      value: totals.verified_apis ?? 0,
      deltaKey: "verified_apis",
      upIsGood: true,
    },
  ];

  const host = document.getElementById("tiles");
  host.replaceChildren();
  for (const spec of specs) {
    const tile = document.createElement("div");
    tile.className = "tile";
    const label = document.createElement("div");
    label.className = "tile-label";
    label.textContent = spec.label;
    const value = document.createElement("div");
    value.className = "tile-value";
    value.textContent = fmtFull(spec.value);
    tile.append(label, value);

    if (
      spec.deltaKey &&
      previous &&
      current &&
      current[spec.deltaKey] != null &&
      previous[spec.deltaKey] != null
    ) {
      const delta = current[spec.deltaKey] - previous[spec.deltaKey];
      const deltaEl = document.createElement("div");
      deltaEl.className = "tile-delta";
      if (delta !== 0) deltaEl.classList.add(delta > 0 ? "up" : "down");
      if (spec.upIsGood === false && delta !== 0) {
        deltaEl.classList.toggle("up", delta < 0);
        deltaEl.classList.toggle("down", delta > 0);
      }
      const sign = delta > 0 ? "+" : "";
      deltaEl.textContent = `${sign}${fmtFull(delta)} ${spec.deltaKey === "verified_apis" ? "APIs" : "lines"} vs previous commit`;
      tile.append(deltaEl);
    }
    host.append(tile);
  }
}

/* ------------------------------------------------------------ line chart */

function renderHistoryChart(points) {
  const host = document.getElementById("history-chart");
  if (!window.echarts) {
    host.innerHTML = "";
    host.append(placeholder("Charts are unavailable (ECharts failed to load)."));
    return;
  }
  if (!points.length) {
    host.innerHTML = "";
    host.append(
      placeholder("No history yet — a data point is recorded on every verified push to main."),
    );
    return;
  }

  const text = baseText();
  const chart = echarts.init(host, null, { renderer: "canvas" });
  const series = SERIES.map((s) => ({
    name: s.name,
    type: "line",
    showSymbol: points.length <= 24,
    symbol: "circle",
    symbolSize: 8,
    itemStyle: { color: css(s.cssVar), borderColor: text.surface, borderWidth: 2 },
    lineStyle: { width: 2, color: css(s.cssVar) },
    emphasis: { focus: "series" },
    dimension: 0,
    data: points.map((p) => [p.date, p[s.key] ?? 0]),
  }));

  chart.setOption({
    animationDuration: 200,
    textStyle: { fontFamily: "system-ui, -apple-system, sans-serif" },
    color: SERIES.map((s) => css(s.cssVar)),
    legend: {
      type: "scroll",
      top: 0,
      icon: "roundRect",
      itemWidth: 12,
      itemHeight: 4,
      textStyle: { color: text.ink2 },
    },
    grid: { left: 56, right: 20, top: 34, bottom: 44 },
    tooltip: {
      trigger: "axis",
      confine: true,
      axisPointer: { type: "line", lineStyle: { color: text.baseline, width: 1 } },
      backgroundColor: text.surface,
      borderColor: "transparent",
      textStyle: { color: text.ink },
      formatter: (params) => {
        const [date] = params[0].value;
        const head = esc(new Date(date).toISOString().slice(0, 10));
        const rows = params
          .slice()
          .sort((a, b) => b.value[1] - a.value[1])
          .map(
            (p) =>
              `<div><span style="display:inline-block;width:10px;height:3px;` +
              `background:${p.color};border-radius:1px;margin-right:5px"></span>` +
              `<span class="tt-label">${esc(p.seriesName)}</span>` +
              ` <span class="tt-value">${fmtFull(p.value[1])}</span></div>`,
          )
          .join("");
        return `<div class="echarts-tooltip">${head}${rows}</div>`;
      },
    },
    xAxis: {
      type: "time",
      axisLine: { lineStyle: { color: text.baseline } },
      axisLabel: { color: text.ink3, hideOverlap: true },
      splitLine: { show: false },
    },
    yAxis: {
      type: "value",
      axisLine: { show: false },
      axisTick: { show: false },
      axisLabel: {
        color: text.ink3,
        formatter: (v) => fmt(v),
      },
      splitLine: { lineStyle: { color: text.grid, width: 1 } },
    },
    series,
  });
  registerChart(chart, host);
}

/* --------------------------------------------------------------- treemap */

/* Module budgets are grouped by subsystem, with an extra platform level under
 * arch. HTML tiles allow status bands and labels to share each module's area. */
function treemapData(snapshot) {
  const mergeModules = (rows) => {
    const merged = { total: 0, spec: 0, proof: 0, rust_mode: 0 };
    for (const st of TM_STATUS) merged[st.key] = 0;
    for (const module of rows) {
      merged.total += module.total;
      merged.spec += module.spec || 0;
      merged.proof += module.proof || 0;
      merged.rust_mode += module.rust_mode || 0;
      for (const st of TM_STATUS) merged[st.key] += module[st.key] || 0;
    }
    return merged;
  };

  const groups = new Map();
  for (const module of snapshot.modules.filter((m) => m.total > 0)) {
    if (!groups.has(module.group)) groups.set(module.group, []);
    groups.get(module.group).push(module);
  }

  const data = [];
  for (const [groupName, rows] of groups) {
    let children;
    if (groupName === "arch") {
      const platforms = new Map();
      for (const module of rows) {
        const [plat, moduleName] = module.child.split("/", 2);
        if (!platforms.has(plat)) platforms.set(plat, new Map());
        const mods = platforms.get(plat);
        if (!mods.has(moduleName)) mods.set(moduleName, []);
        mods.get(moduleName).push(module);
      }
      children = [...platforms.entries()]
        .map(([plat, mods]) => {
          const leaves = [...mods.entries()]
            .map(([name, rows]) => ({ name, level: "module", ...mergeModules(rows) }))
            .sort((a, b) => b.total - a.total || a.name.localeCompare(b.name));
          return {
            name: plat,
            level: "platform",
            ...mergeModules(leaves),
            children: leaves,
          };
        })
        .sort((a, b) => b.total - a.total || a.name.localeCompare(b.name));
    } else {
      children = [...new Map(rows.map((m) => [m.child, rows.filter((r) => r.child === m.child)]))
        .entries()]
        .map(([name, rows]) => ({ name, level: "module", ...mergeModules(rows) }))
        .sort((a, b) => b.total - a.total || a.name.localeCompare(b.name));
    }
    data.push({
      name: groupName,
      level: "group",
      ...mergeModules(children),
      children,
    });
  }
  data.sort((a, b) => b.total - a.total);
  return data;
}

/* Squarified treemap layout (reference: code_treemap.py squarify()). */
function squarifyRects(sizes, rect) {
  const total = sizes.reduce((sum, value) => sum + value, 0);
  if (total <= 0 || rect.w <= 0 || rect.h <= 0) return [];
  const area = rect.w * rect.h;
  const rest = sizes.map((value) => (value * area) / total);
  const out = [];
  let bounds = { ...rect };

  const worstRatio = (row, side) => {
    if (!row.length || Math.min(...row) <= 0 || side <= 0) return Infinity;
    const rowSum = row.reduce((s, v) => s + v, 0);
    return Math.max(
      (side * side * Math.max(...row)) / (rowSum * rowSum),
      (rowSum * rowSum) / (side * side * Math.min(...row)),
    );
  };

  while (rest.length) {
    const row = [rest.shift()];
    const side = Math.min(bounds.w, bounds.h);
    while (rest.length) {
      const candidate = row.concat(rest[0]);
      if (worstRatio(candidate, side) > worstRatio(row, side)) break;
      row.push(rest.shift());
    }
    const rowSum = row.reduce((s, v) => s + v, 0);
    if (bounds.w >= bounds.h) {
      const rowWidth = rowSum / bounds.h;
      let cursorY = bounds.y;
      for (const size of row) {
        const itemHeight = size / rowWidth;
        out.push({ x: bounds.x, y: cursorY, w: rowWidth, h: itemHeight });
        cursorY += itemHeight;
      }
      bounds = { x: bounds.x + rowWidth, y: bounds.y, w: bounds.w - rowWidth, h: bounds.h };
    } else {
      const rowHeight = rowSum / bounds.w;
      let cursorX = bounds.x;
      for (const size of row) {
        const itemWidth = size / rowHeight;
        out.push({ x: cursorX, y: bounds.y, w: itemWidth, h: rowHeight });
        cursorX += itemWidth;
      }
      bounds = { x: bounds.x, y: bounds.y + rowHeight, w: bounds.w, h: bounds.h - rowHeight };
    }
  }
  return out;
}

// A single HTML tooltip works for modules, group captions, keyboard and touch.
function renderTreemapChart(snapshot) {
  const host = document.getElementById("treemap-chart");
  renderTreemapLegend(snapshot);
  host.replaceChildren();
  const root = document.createElement("div");
  root.className = "tm-root";
  const tooltip = document.createElement("div");
  tooltip.className = "tm-tooltip";
  tooltip.id = "module-tooltip";
  tooltip.setAttribute("role", "tooltip");
  tooltip.hidden = true;
  host.append(root, tooltip);

  const W = host.clientWidth;
  const H = host.clientHeight;
  if (!W || !H) return;
  const HEADER = 22;
  const GAP = { group: 4, platform: 2, module: 1 };
  const inset = (rect, pad) => ({
    x: rect.x + pad, y: rect.y + pad,
    w: Math.max(0, rect.w - 2 * pad), h: Math.max(0, rect.h - 2 * pad),
  });
  const place = (rect, className) => {
    const el = document.createElement("div");
    el.className = className;
    Object.assign(el.style, {
      left: `${rect.x}px`, top: `${rect.y}px`,
      width: `${rect.w}px`, height: `${rect.h}px`,
    });
    root.append(el);
    return el;
  };
  const moveTooltip = (x, y) => {
    // Fixed coordinates keep the card inside the viewport at the bottom/right.
    const margin = 12;
    tooltip.style.left = `${Math.max(margin, Math.min(x + margin, window.innerWidth - tooltip.offsetWidth - margin))}px`;
    tooltip.style.top = `${Math.max(margin, Math.min(y + margin, window.innerHeight - tooltip.offsetHeight - margin))}px`;
  };
  const describe = (el, node, path) => {
    el.tabIndex = 0;
    el.setAttribute("aria-label", `${path}, ${fmtFull(node.total)} executable lines`);
    el.setAttribute("aria-describedby", tooltip.id);
    const show = (event) => {
      tooltip.innerHTML = `<strong>${esc(path)}</strong>` + TM_STATUS.map((st) =>
        `<div class="tm-tooltip-row"><span class="legend-swatch" style="background:var(${st.cssVar})"></span>` +
        `<span>${esc(st.key === "verified_exec" ? "Verified" : st.name)}</span>` +
        `<b>${fmtFull(node[st.key] || 0)}</b><span>LoC</span></div>`).join("") +
        `<div class="tm-tooltip-meta">${fmtFull(node.total)} exec LoC · spec ${fmtFull(node.spec)} · proof ${fmtFull(node.proof)}<br>` +
        `VOSTD rust-mode ${fmtFull(node.rust_mode)}</div>`;
      tooltip.hidden = false;
      const rect = el.getBoundingClientRect();
      moveTooltip(event.clientX ?? rect.left, event.clientY ?? rect.bottom);
    };
    el.addEventListener("pointerenter", show);
    el.addEventListener("pointermove", (e) => moveTooltip(e.clientX, e.clientY));
    el.addEventListener("pointerleave", () => { tooltip.hidden = true; });
    el.addEventListener("focus", show);
    el.addEventListener("blur", () => { tooltip.hidden = true; });
    el.addEventListener("click", show);
    el.addEventListener("keydown", (e) => { if (e.key === "Escape") tooltip.hidden = true; });
  };
  const drawModule = (node, rect, path, collapsed = false) => {
    if (rect.w < 1 || rect.h < 1) return;
    const cell = place(rect, "tm-module");
    describe(cell, node, path);
    for (const st of TM_STATUS.slice().reverse()) {
      if (!node[st.key]) continue;
      const band = document.createElement("div");
      band.className = "tm-status";
      band.style.flexGrow = String(node[st.key]);
      band.style.background = `var(${st.cssVar})`;
      cell.append(band);
    }
    if (rect.w >= 28 && rect.h >= 16) {
      const label = document.createElement("div");
      label.className = "tm-label";
      label.style.fontSize = `${rect.w > 180 && rect.h > 100 ? 20 : rect.w > 95 && rect.h > 50 ? 15 : 11}px`;
      if (collapsed) {
        label.classList.add("tm-label-group");
        label.style.fontSize = `${Math.min(10, (rect.w - 6) / (node.name.length * 0.72))}px`;
        const name = document.createElement("span");
        name.className = "tm-group-name";
        name.textContent = node.name.toUpperCase();
        const count = document.createElement("span");
        count.className = "tm-group-total";
        count.textContent = `${fmtFull(node.total)} LoC`;
        label.append(name, count);
      } else {
        label.textContent = node.name;
      }
      cell.append(label);
    }
  };
  const layout = (nodes, bounds, gap, prefix, fixedRects) => {
    if (bounds.w <= 0 || bounds.h <= 0) return;
    let rects = fixedRects || squarifyRects(nodes.map((node) => node.total), bounds);
    // Keep the main architecture beside the other platforms, as in the overview.
    if (nodes[0]?.level === "platform" && nodes.length > 1 && bounds.w > bounds.h) {
      const total = nodes.reduce((sum, node) => sum + node.total, 0);
      const width = bounds.w * nodes[0].total / total;
      const rest = { x: bounds.x + width, y: bounds.y, w: bounds.w - width, h: bounds.h };
      let y = rest.y;
      rects = [{ ...bounds, w: width }, ...nodes.slice(1).map((node) => {
        const h = rest.h * node.total / (total - nodes[0].total);
        const rect = { ...rest, y, h };
        y += h;
        return rect;
      })];
    }
    nodes.forEach((node, i) => {
      const rect = inset(rects[i], gap / 2);
      const path = prefix ? `${prefix}/${node.name}` : node.name;
      if (node.level === "module") {
        drawModule(node, rect, path);
        return;
      }
      // Tiny groups keep their status colors instead of becoming clipped headers.
      if (rect.w < 64 || rect.h < HEADER + 20) {
        drawModule(node, rect, path, true);
        return;
      }
      place(rect, "tm-group");
      const band = place({ ...rect, h: HEADER }, "tm-header");
      band.textContent = `${node.name.toUpperCase()} | ${fmtFull(node.total)} LoC`;
      describe(band, node, path);
      layout(node.children,
        { x: rect.x + 1, y: rect.y + HEADER, w: rect.w - 2, h: rect.h - HEADER - 1 },
        node.level === "group" ? GAP.platform : GAP.module, path);
    });
  };
  const data = treemapData(snapshot);
  if (W >= 700 && data[0]?.name === "arch" && data[1]?.name === "mm") {
    const leftTotal = data[0].total + data[1].total;
    const width = W * leftTotal / data.reduce((sum, node) => sum + node.total, 0);
    const height = H * data[0].total / leftTotal;
    layout(data.slice(0, 2), { x: 0, y: 0, w: width, h: H }, GAP.group, "", [
      { x: 0, y: 0, w: width, h: height },
      { x: 0, y: height, w: width, h: H - height },
    ]);
    const right = data.slice(2);
    const small = right.filter((node) => node.total < 100);
    const large = right.filter((node) => node.total >= 100);
    const rightTotal = right.reduce((sum, node) => sum + node.total, 0);
    const smallTotal = small.reduce((sum, node) => sum + node.total, 0);
    // A shallow row gives small subsystem names more width without enlarging
    // their areas or forcing the chart beyond the viewport.
    const rowHeight = H * smallTotal / rightTotal;
    layout(large, { x: width, y: 0, w: W - width, h: H - rowHeight }, GAP.group, "");
    let x = width;
    const smallRects = small.map((node) => {
      const w = (W - width) * node.total / smallTotal;
      const rect = { x, y: H - rowHeight, w, h: rowHeight };
      x += w;
      return rect;
    });
    layout(small, { x: width, y: H - rowHeight, w: W - width, h: rowHeight }, GAP.group, "", smallRects);
  } else {
    layout(data, { x: 0, y: 0, w: W, h: H }, GAP.group, "");
  }
}

function renderTreemapLegend(snapshot) {
  const host = document.getElementById("treemap-legend");
  if (!host) return;
  const totals = snapshot.totals;
  const total = totals.total || 1;
  host.replaceChildren(
    ...TM_STATUS.map((st) => {
      const chip = document.createElement("span");
      chip.className = "legend-chip";
      const swatch = document.createElement("span");
      swatch.className = "legend-swatch";
      swatch.style.background = css(st.cssVar);
      chip.append(swatch, document.createTextNode(
        `${st.name} ${PCT((totals[st.key] || 0) / total)}`,
      ));
      return chip;
    }),
  );
}

/* ---------------------------------------------------------------- tables */

function table(rows, headers) {
  const t = document.createElement("table");
  t.className = "grid";
  const thead = t.createTHead();
  const headRow = thead.insertRow();
  for (const h of headers) {
    const th = document.createElement("th");
    th.textContent = h;
    headRow.append(th);
  }
  const tbody = t.createTBody();
  for (const row of rows) {
    const tr = tbody.insertRow();
    for (const cell of row) {
      const td = tr.insertCell();
      if (cell instanceof Node) td.append(cell);
      else td.textContent = cell;
    }
  }
  return t;
}

function renderTreemapTable(snapshot) {
  const host = document.getElementById("treemap-table");
  host.replaceChildren(
    table(
      snapshot.modules
        .slice()
        .sort((a, b) =>
          `${a.group}/${a.child}`.localeCompare(`${b.group}/${b.child}`))
        .map((m) => [
          `${m.group}/${m.child}`,
          fmtFull(m.total),
          fmtFull(m.verified_exec),
          fmtFull(m.trusted),
          fmtFull(m.unverified),
          fmtFull(m.unplanned),
          PCT(m.total ? m.verified_exec / m.total : 0),
        ]),
      ["Module", "Exec LoC", "Verified", "Trusted boundary", "Unverified", "Unplanned", "Verified share"],
    ),
  );
}

function renderHistoryTable(points) {
  const host = document.getElementById("history-table");
  host.replaceChildren(
    table(
      points
        .slice()
        .reverse()
        .map((p) => [
          (p.date || "").slice(0, 10),
          String(p.sha || "").slice(0, 8),
          fmtFull(p.verified_exec ?? 0),
          fmtFull(p.trusted ?? 0),
          fmtFull(p.spec ?? 0),
          fmtFull(p.proof ?? 0),
          p.verified_apis != null ? fmtFull(p.verified_apis) : "—",
        ]),
      ["Date", "Commit", "Verified", "Trusted boundary", "Spec", "Proof", "Verified APIs"],
    ),
  );
}

function renderApiTable(snapshot) {
  const host = document.getElementById("api-table");
  const entries = Array.isArray(snapshot.verified_apis_list)
    ? snapshot.verified_apis_list
    : [];
  if (!entries.length) {
    host.replaceChildren(
      placeholder(
        "This snapshot carries no API list — the rustdoc JSON step has not run for it yet.",
      ),
    );
    return;
  }
  host.replaceChildren(
    table(
      entries
        .slice()
        .sort((a, b) =>
          (a.group + a.name).localeCompare(b.group + b.name))
        .map((api) => {
          const link = document.createElement("a");
          link.textContent = api.name;
          // Snapshot links are relative to the published documentation root.
          if (api.doc_path && !api.doc_path.split("/").includes("..") &&
              /^[a-zA-Z0-9_./#%~-]+$/.test(api.doc_path)) {
            link.href = `verusdoc/${api.doc_path}`;
          }
          return [link, api.group, api.location];
        }),
      ["Verified API", "Module", "Location"],
    ),
  );
}

/* ------------------------------------------------------------- plumbing */

function placeholder(message) {
  const el = document.createElement("p");
  el.className = "chart-placeholder";
  el.textContent = message;
  return el;
}

const liveCharts = [];
const liveData = {};

function registerChart(chart, host) {
  liveCharts.push([chart, host]);
}

function disposeCharts() {
  for (const [chart] of liveCharts) chart.dispose();
  liveCharts.length = 0;
}

async function loadJson(url) {
  const response = await fetch(url);
  if (!response.ok) return null;
  return response.json();
}

async function main() {
  const [snapshot, history] = await Promise.all([
    loadJson("stats/snapshot.json"),
    loadJson("stats/history.json"),
  ]);

  if (!snapshot) {
    document.getElementById("snapshot-meta").textContent =
      "statistics unavailable for this deployment";
    const tiles = document.getElementById("tiles");
    tiles.replaceChildren(
      placeholder("No snapshot — the stats job did not publish data for this run."),
    );
    document.getElementById("treemap-chart").replaceChildren(placeholder("No snapshot."));
    document.getElementById("history-chart").replaceChildren(placeholder("No history."));
    return;
  }
  liveData.snapshot = snapshot;
  liveData.points = history && Array.isArray(history.points) ? history.points : [];

  const shaShort = String(snapshot.sha || "").slice(0, 8);
  document.getElementById("snapshot-meta").textContent =
    `snapshot ${shaShort} · ${fmtFull(snapshot.totals.total)} executable LoC budget` +
    (snapshot.mainline_sha ? ` · mainline ${String(snapshot.mainline_sha).slice(0, 8)}` : "");

  renderTiles(snapshot, liveData.points);
  renderHistoryChart(liveData.points);
  renderTreemapChart(snapshot);
  renderHistoryTable(liveData.points);
  renderTreemapTable(snapshot);
  renderApiTable(snapshot);

  let resizeFrame;
  const observer = new ResizeObserver(() => {
    cancelAnimationFrame(resizeFrame);
    resizeFrame = requestAnimationFrame(() => {
      for (const [chart] of liveCharts) chart.resize();
      renderTreemapChart(liveData.snapshot);
    });
  });
  observer.observe(document.getElementById("treemap-chart"));

  const scheme = window.matchMedia("(prefers-color-scheme: dark)");
  scheme.addEventListener("change", () => {
    disposeCharts();
    renderHistoryChart(liveData.points);
    renderTreemapChart(liveData.snapshot);
  });
}

main().catch((error) => {
  document.getElementById("snapshot-meta").textContent = "failed to load stats";
  console.error(error);
});
