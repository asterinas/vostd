window.BENCHMARK_DATA = {
  "lastUpdate": 1789195636123,
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
      }
    ]
  }
}