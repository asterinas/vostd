window.BENCHMARK_DATA = {
  "lastUpdate": 1789272826341,
  "repoUrl": "https://github.com/asterinas/vostd",
  "entries": {
    "verify-perf": [
      {
        "commit": {
          "author": {
            "email": "22045841+Marsman1996@users.noreply.github.com",
            "name": "Yuwei LIU",
            "username": "Marsman1996"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "4a4c0d7983d72dcc63d41b0087619163b73ef626",
          "message": "ci: add perf ci and macOS for upstream (#759)\n\n* ci: add perf ci\n\n* ci: merge macos into ci.yml\n\n* ci: add macOS for upstream test\n\n* ci: chart verus verify cost on in-repo gh-pages + rlimit alerts\n\n* ci: add perf data into doc",
          "timestamp": "2026-09-12T14:34:49+08:00",
          "tree_id": "bb6a50a67ef640c9a9dab25575a8e1c89beaae3e",
          "url": "https://github.com/asterinas/vostd/commit/4a4c0d7983d72dcc63d41b0087619163b73ef626"
        },
        "date": 1789195634634,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1617456838,
            "unit": "rlimit",
            "extra": "verified=4080 errors=0 smt-run=533,710ms wall=304,188ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 752109709,
            "unit": "rlimit",
            "extra": "smt-run=262,193ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 202464146,
            "unit": "rlimit",
            "extra": "smt-run=36,937ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 130778633,
            "unit": "rlimit",
            "extra": "smt-run=76,921ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,713ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9250300,
            "unit": "rlimit",
            "extra": "smt-run=2,577ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,707ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,189ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=902ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=634ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "22045841+Marsman1996@users.noreply.github.com",
            "name": "Yuwei LIU",
            "username": "Marsman1996"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d3f18cf0eff92f0af5b6948e6fd07a732610e8d2",
          "message": "performance: opaque `pt_inv_at_depth` (#760)",
          "timestamp": "2026-09-12T21:03:20+08:00",
          "tree_id": "013eb54aafcc5b8d3c6842f09fd6030efc834973",
          "url": "https://github.com/asterinas/vostd/commit/d3f18cf0eff92f0af5b6948e6fd07a732610e8d2"
        },
        "date": 1789218549645,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1428694052,
            "unit": "rlimit",
            "extra": "verified=4080 errors=0 smt-run=490,580ms wall=288,636ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 571710626,
            "unit": "rlimit",
            "extra": "smt-run=227,899ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 202464146,
            "unit": "rlimit",
            "extra": "smt-run=40,394ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 123794456,
            "unit": "rlimit",
            "extra": "smt-run=74,671ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,557ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9250300,
            "unit": "rlimit",
            "extra": "smt-run=2,273ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,576ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,092ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=849ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=558ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "22045841+Marsman1996@users.noreply.github.com",
            "name": "Yuwei LIU",
            "username": "Marsman1996"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "99243fb935e07c2de21ca4efbf041a12144dc086",
          "message": "chore: drop btree spec superseded by upstream vstd and update CIs (#762)\n\n* chore: drop btree spec superseded by upstream vstd\n\n* ci: add PR merge for upstream test\n\n* ci: show verify-perf in checks when comment on the PR\n\n* ci: post ci/doc commit status for workflow_run doc builds",
          "timestamp": "2026-09-13T11:44:35+08:00",
          "tree_id": "e8161523168706fd101bf150dcae10c941837922",
          "url": "https://github.com/asterinas/vostd/commit/99243fb935e07c2de21ca4efbf041a12144dc086"
        },
        "date": 1789272825725,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1428938614,
            "unit": "rlimit",
            "extra": "verified=4080 errors=0 smt-run=352,148ms wall=217,181ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 571710626,
            "unit": "rlimit",
            "extra": "smt-run=163,094ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 202464146,
            "unit": "rlimit",
            "extra": "smt-run=28,587ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 123794456,
            "unit": "rlimit",
            "extra": "smt-run=56,883ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,086ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,669ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,148ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=816ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=540ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=374ms"
          }
        ]
      }
    ]
  }
}