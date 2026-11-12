"use strict";

(() => {
  const runs = (window.BENCHMARK_DATA?.entries?.["verify-perf"] || [])
    .slice().sort((a, b) => a.date - b.date);
  const full = (n) => new Intl.NumberFormat("en").format(n);
  const css = (name) => getComputedStyle(document.documentElement).getPropertyValue(name).trim();
  const esc = (s) => String(s).replace(/[&<>"']/g, (c) =>
    ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
  const metric = (run, name) => run?.benches.find((b) => b.name === name);
  const meta = document.getElementById("bench-meta");
  if (!runs.length) {
    meta.textContent = "No benchmark history yet. Measurements appear after the first successful performance run.";
    return;
  }
  const latest = runs.at(-1);
  const previous = runs.at(-2);
  meta.textContent = `snapshot ${latest.commit.id.slice(0, 8)} · ${new Date(latest.date).toISOString().slice(0, 10)} · ${runs.length} recorded runs`;
  const total = metric(latest, "total rlimit");
  const extra = total?.extra || "";
  const stat = (key) => extra.match(new RegExp(`${key}=([\\d,]+)`))?.[1];
  const tiles = [
    ["Total rlimit", total ? full(total.value) : "—"],
    ["Verified obligations", stat("verified") || "—"],
    ["Solver time", stat("smt-run") ? `${(Number(stat("smt-run").replaceAll(",", "")) / 1000).toFixed(1)} s` : "—"],
    ["Wall time", stat("wall") ? `${(Number(stat("wall").replaceAll(",", "")) / 1000).toFixed(1)} s` : "—"],
  ];
  for (const [label, value] of tiles) {
    const tile = document.createElement("div");
    tile.className = "tile";
    tile.innerHTML = `<div class="tile-label">${esc(label)}</div><div class="tile-value">${esc(value)}</div>`;
    document.getElementById("bench-tiles").append(tile);
  }

  const table = document.createElement("table");
  table.className = "grid";
  table.innerHTML = "<thead><tr><th>Measurement</th><th>rlimit</th><th>vs previous run</th></tr></thead>";
  const body = table.createTBody();
  for (const bench of latest.benches) {
    const row = body.insertRow();
    const old = metric(previous, bench.name);
    const delta = old && old.value > 0 ? (bench.value - old.value) / old.value : null;
    const change = delta == null ? "—" : `${delta > 0 ? "+" : ""}${(delta * 100).toFixed(1)}%`;
    row.insertCell().textContent = bench.name.replace(/^rlimit: /, "");
    row.insertCell().textContent = full(bench.value);
    const cell = row.insertCell();
    cell.textContent = change;
    if (delta) cell.style.color = css(delta < 0 ? "--good-text" : "--bad-text");
  }
  document.getElementById("bench-table").append(table);

  const charts = [];
  function draw(hostId, names, selected) {
    const host = document.getElementById(hostId);
    if (!window.echarts) {
      host.innerHTML = '<p class="chart-placeholder">Charts are unavailable (ECharts failed to load). Latest measurements are listed below.</p>';
      return;
    }
    const chart = echarts.init(host);
    charts.push(chart);
    chart.setOption({
      color: ["--series-verified", "--series-trusted", "--series-spec", "--series-proof", "--series-api"].map(css),
      textStyle: { fontFamily: "system-ui, -apple-system, sans-serif", color: css("--ink-2") },
      legend: { show: names.length > 1, type: "scroll", top: 8, selected, textStyle: { color: css("--ink-2") }, pageTextStyle: { color: css("--ink-2") } },
      grid: { left: 65, right: 24, top: 55, bottom: 75 },
      tooltip: {
        trigger: "axis", confine: true, backgroundColor: css("--surface-1"), borderColor: css("--baseline"), textStyle: { color: css("--ink") },
        formatter: (params) => {
          const run = runs[params[0].dataIndex];
          return `<strong>${esc(run.commit.id.slice(0, 8))}</strong> · ${esc(new Date(run.date).toISOString().slice(0, 10))}<br>` +
            esc(run.commit.message.split("\n")[0]) + "<br>" +
            params.filter((p) => p.value != null).map((p) => `${p.marker}${esc(p.seriesName)}: <b>${full(p.value)}</b> rlimit`).join("<br>");
        },
      },
      xAxis: { type: "category", data: runs.map((r) => r.commit.id.slice(0, 8)), axisLabel: { color: css("--ink-3"), hideOverlap: true }, axisLine: { lineStyle: { color: css("--baseline") } } },
      yAxis: { type: "value", axisLabel: { color: css("--ink-3"), formatter: (v) => new Intl.NumberFormat("en", { notation: "compact" }).format(v) }, splitLine: { lineStyle: { color: css("--grid") } } },
      dataZoom: [{ type: "slider", bottom: 12, height: 20, borderColor: css("--border"), backgroundColor: css("--surface-1"), fillerColor: css("--grid"), dataBackground: { lineStyle: { color: css("--ink-3") }, areaStyle: { color: css("--grid") } }, textStyle: { color: css("--ink-2") } }],
      series: names.map((name) => ({
        name: name.replace(/^rlimit: /, ""), type: "line", symbol: "circle", symbolSize: 7,
        connectNulls: false, data: runs.map((r) => metric(r, name)?.value ?? null),
      })),
    });
    chart.on("click", (p) => {
      const url = runs[p.dataIndex]?.commit.url;
      if (url && /^https:\/\/github\.com\//.test(url)) window.open(url, "_blank", "noopener");
    });
  }
  function render() {
    charts.splice(0).forEach((chart) => chart.dispose());
    draw("bench-total", ["total rlimit"]);
    const names = [...new Set(runs.flatMap((r) => r.benches.map((b) => b.name)))].filter((name) => name !== "total rlimit")
      .sort((a, b) => (metric(latest, b)?.value ?? -1) - (metric(latest, a)?.value ?? -1) || a.localeCompare(b));
    const top = latest.benches.filter((b) => b.name !== "total rlimit").sort((a, b) => b.value - a.value).slice(0, 5).map((b) => b.name);
    draw("bench-modules", names, Object.fromEntries(names.map((name) => [name.replace(/^rlimit: /, ""), top.includes(name)])));
  }
  render();
  new ResizeObserver(() => charts.forEach((chart) => chart.resize())).observe(document.querySelector(".wrap"));
  window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", render);
})();
