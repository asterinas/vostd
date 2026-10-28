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
];

const TM_STATUS = [
  { key: "verified_exec", name: "Verified", cssVar: "--tm-verified", darkText: true },
  { key: "trusted", name: "Trusted", cssVar: "--tm-trusted", darkText: true },
  { key: "unverified", name: "Unverified", cssVar: "--tm-unverified", darkText: false },
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
    { label: "Unverified", value: totals.unverified, deltaKey: "unverified", upIsGood: false },
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
    value.textContent = fmt(spec.value);
    tile.append(label, value);

    if (spec.deltaKey && previous && current && current[spec.deltaKey] != null) {
      const delta = current[spec.deltaKey] - previous[spec.deltaKey];
      const deltaEl = document.createElement("div");
      deltaEl.className = "tile-delta";
      if (delta !== 0) deltaEl.classList.add(delta > 0 ? "up" : "down");
      if (spec.upIsGood === false && delta !== 0) {
        deltaEl.classList.toggle("up", delta < 0);
        deltaEl.classList.toggle("down", delta > 0);
      }
      const sign = delta > 0 ? "+" : "";
      deltaEl.textContent = `${sign}${fmtFull(delta)} lines vs previous commit`;
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
      top: 0,
      icon: "roundRect",
      itemWidth: 12,
      itemHeight: 4,
      textStyle: { color: text.ink2 },
    },
    grid: { left: 56, right: 20, top: 34, bottom: 44 },
    tooltip: {
      trigger: "axis",
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

function renderTreemapChart(snapshot) {
  const host = document.getElementById("treemap-chart");
  if (!window.echarts) {
    host.innerHTML = "";
    host.append(placeholder("Charts are unavailable (ECharts failed to load)."));
    return;
  }

  const text = baseText();
  const byGroup = new Map();
  for (const module of snapshot.modules) {
    const key = `${module.group}/${module.child}`;
    const node = {
      name: module.child,
      meta: module,
      children: TM_STATUS.map((st) => ({
        name: st.name,
        value: module[st.key],
        itemStyle: { color: css(st.cssVar) },
      })),
    };
    if (!byGroup.has(module.group)) byGroup.set(module.group, []);
    byGroup.get(module.group).push(node);
  }

  const data = [...byGroup.entries()].map(([group, children]) => ({ name: group, children }));

  const chart = echarts.init(host);
  chart.setOption({
    animationDuration: 200,
    textStyle: { fontFamily: "system-ui, -apple-system, sans-serif" },
    tooltip: {
      backgroundColor: text.surface,
      borderColor: "transparent",
      textStyle: { color: text.ink },
      confine: true,
      formatter: (info) => {
        const module = info.data.meta;
        if (!module) return "";
        const matched = module.files_with_mainline === module.files;
        const rows = TM_STATUS.map(
          (st) =>
            `<div><span style="display:inline-block;width:10px;height:10px;` +
            `background:${css(st.cssVar)};border-radius:2px;margin-right:6px"></span>` +
            `<span class="tt-label">${st.name}</span> <span class="tt-value">${fmtFull(
              module[st.key],
            )}</span></div>`,
        ).join("");
        const shaft = `<div class="tt-label" style="margin-top:4px">` +
          `spec ${fmtFull(module.spec)} · proof ${fmtFull(module.proof)} · vostd rust-mode ` +
          `${fmtFull(module.rust_mode)}${matched ? "" : " · not in mainline"}</div>`;
        return `<div class="echarts-tooltip"><div class="tt-value">${esc(
          module.group,
        )}/${esc(module.child)}</div>${rows}${shaft}</div>`;
      },
    },
    series: [
      {
        type: "treemap",
        roam: false,
        nodeClick: "zoomToNode",
        breadcrumb: {
          show: true,
          bottom: 0,
          itemStyle: { color: text.surface, borderColor: text.baseline, textStyle: { color: text.ink2 } },
        },
        label: { show: true, formatter: "{b}", fontSize: 11, color: text.ink },
        upperLabel: {
          show: true,
          height: 20,
          fontSize: 11,
          color: text.ink2,
          fontWeight: 600,
        },
        itemStyle: { borderColor: text.surface, borderWidth: 2, gapWidth: 2 },
        levels: [
          { itemStyle: { borderColor: text.surface, borderWidth: 0, gapWidth: 3 } },
          {
            itemStyle: {
              borderColor: text.surface,
              borderWidth: 2,
              gapWidth: 2,
              color: text.grid,
            },
          },
          { colorSaturation: [0, 0], itemStyle: { borderWidth: 1, gapWidth: 1, borderColor: text.surface } },
        ],
        data,
      },
    ],
  });
  registerChart(chart, host);
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
      td.textContent = cell;
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
        .sort((a, b) => b.total - a.total)
        .map((m) => [
          `${m.group}/${m.child}`,
          fmtFull(m.total),
          fmtFull(m.verified_exec),
          fmtFull(m.trusted),
          fmtFull(m.unverified),
          PCT(m.total ? m.verified_exec / m.total : 0),
        ]),
      ["Module", "Exec LoC", "Verified", "Trusted", "Unverified", "Verified share"],
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
        ]),
      ["Date", "Commit", "Verified", "Trusted", "Spec", "Proof"],
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

function rerender() {
  liveCharts.length = 0; // disposed below
  renderHistoryChart(liveData.points || []);
  renderTreemapChart(liveData.snapshot);
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
