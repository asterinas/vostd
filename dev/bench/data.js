window.BENCHMARK_DATA = {
  "lastUpdate": 1794634464265,
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
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bc7200b7a8e3d65c33e072f671a2cb1c2fe9bbc8",
          "message": "performance (#761)\n\n* performance\n\n* minor\n\n* remove some proofs\n\n* more simplify\n\n* perf\n\n* simplify\n\n* Update ci-irc11.yml\n\n* fix lemma names",
          "timestamp": "2026-09-13T20:21:58+08:00",
          "tree_id": "4f3c411ebd16bea51e8fe2e28f4a896ec5b78062",
          "url": "https://github.com/asterinas/vostd/commit/bc7200b7a8e3d65c33e072f671a2cb1c2fe9bbc8"
        },
        "date": 1789302429964,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1038206533,
            "unit": "rlimit",
            "extra": "verified=4081 errors=0 smt-run=281,467ms wall=202,704ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 333202113,
            "unit": "rlimit",
            "extra": "smt-run=112,994ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 85126605,
            "unit": "rlimit",
            "extra": "smt-run=26,116ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 51152450,
            "unit": "rlimit",
            "extra": "smt-run=20,053ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,314ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,089ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,309ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,020ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=701ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=496ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "4576a9795c4bdeeee6f48bdc1540c710053f14aa",
          "message": "Prove simple kvirt area obligations (#739)\n\nCo-authored-by: Je5s1e <chaoccc22@gmail.com>",
          "timestamp": "2026-09-14T11:17:10+08:00",
          "tree_id": "6b31e604ffe8ad860eed023809a05f163823ced5",
          "url": "https://github.com/asterinas/vostd/commit/4576a9795c4bdeeee6f48bdc1540c710053f14aa"
        },
        "date": 1789356399329,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1038072806,
            "unit": "rlimit",
            "extra": "verified=4081 errors=0 smt-run=253,229ms wall=175,344ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 333202113,
            "unit": "rlimit",
            "extra": "smt-run=102,619ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 85126605,
            "unit": "rlimit",
            "extra": "smt-run=22,188ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 63643368,
            "unit": "rlimit",
            "extra": "smt-run=21,163ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,102ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,858ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,239ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=873ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=671ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=471ms"
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
          "id": "c05e6480d2008ffdb8e011181f70454feccfcd9a",
          "message": "simplify: mm::page_table::cursor (#763)",
          "timestamp": "2026-09-14T11:29:09+08:00",
          "tree_id": "4e93557bdc43d75fb6f46f932f2622d02fa093cb",
          "url": "https://github.com/asterinas/vostd/commit/c05e6480d2008ffdb8e011181f70454feccfcd9a"
        },
        "date": 1789356841164,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1010200239,
            "unit": "rlimit",
            "extra": "verified=4081 errors=0 smt-run=335,018ms wall=230,273ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 305329546,
            "unit": "rlimit",
            "extra": "smt-run=129,713ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 85126605,
            "unit": "rlimit",
            "extra": "smt-run=32,652ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 63643368,
            "unit": "rlimit",
            "extra": "smt-run=27,182ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,658ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,365ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,635ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,154ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=800ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=645ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a6552fc47244d9ac3c2f851b3419a3b23cc1abd1",
          "message": "chore: remove several redundant `InvView` implementations (#764)\n\n* chore: remove `NodeModel`\n\n* chore: remove `EntryView`",
          "timestamp": "2026-09-14T15:23:09+08:00",
          "tree_id": "b5886953fa438a9dba417cd59cdcbbe1eef80728",
          "url": "https://github.com/asterinas/vostd/commit/a6552fc47244d9ac3c2f851b3419a3b23cc1abd1"
        },
        "date": 1789371306134,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1075909141,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=266,990ms wall=181,146ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 369104275,
            "unit": "rlimit",
            "extra": "smt-run=111,721ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 87683492,
            "unit": "rlimit",
            "extra": "smt-run=23,095ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86123454,
            "unit": "rlimit",
            "extra": "smt-run=20,234ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,265ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,801ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,308ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=857ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=595ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=458ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "96a1b1f968703618427fd04e3eabc790a788d8f8",
          "message": "fix: `Frame::meta` (#765)\n\n* fix: `Frame::meta`\n\n* fix `PageTableNode::level`\n\n* fix `PageTableNode::nr_children`\n\n* fix: `Entry::is_node`",
          "timestamp": "2026-09-14T19:54:22+08:00",
          "tree_id": "ae5bfb8a7640c6767922bc1b6f4f40b83f9fe4e5",
          "url": "https://github.com/asterinas/vostd/commit/96a1b1f968703618427fd04e3eabc790a788d8f8"
        },
        "date": 1789387168502,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1070545411,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=355,229ms wall=227,802ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 371411986,
            "unit": "rlimit",
            "extra": "smt-run=145,696ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86512060,
            "unit": "rlimit",
            "extra": "smt-run=30,987ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80760641,
            "unit": "rlimit",
            "extra": "smt-run=31,799ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,724ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,529ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,600ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,188ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=918ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=623ms"
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
          "id": "e3b0444ac4ef64723fba9e21c9a41c72a3937d94",
          "message": "ci: refactor ci workflow (#766)",
          "timestamp": "2026-09-14T22:41:53+08:00",
          "tree_id": "04105e59eb49d6ccffdf1cb5750d3ab4d1b22596",
          "url": "https://github.com/asterinas/vostd/commit/e3b0444ac4ef64723fba9e21c9a41c72a3937d94"
        },
        "date": 1789397924088,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1070545411,
            "unit": "rlimit",
            "extra": "verified=4079 errors=0 smt-run=368,976ms wall=237,950ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 371411986,
            "unit": "rlimit",
            "extra": "smt-run=149,033ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86512060,
            "unit": "rlimit",
            "extra": "smt-run=39,931ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80760641,
            "unit": "rlimit",
            "extra": "smt-run=34,764ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,588ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,301ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,525ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,116ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=794ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=545ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c7e0549310263adf5622ce3f3eaade1c28037689",
          "message": "chore: remove unused lemmas and remove `level` in `NodeOwner` (#767)\n\n* chore: remove `level` in `NodeOwner`\n\n* remove a unnecessary condition\n\n* minor\n\n* remove `PageMetaModel`\n\n* Remove unused lemmas\n\n* remove more\n\n* clean more\n\n* remove more",
          "timestamp": "2026-09-15T14:55:35+08:00",
          "tree_id": "8f3e1657f9fd0513901bb0a676549a22a0f1e88e",
          "url": "https://github.com/asterinas/vostd/commit/c7e0549310263adf5622ce3f3eaade1c28037689"
        },
        "date": 1789456015491,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1070315358,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=347,639ms wall=223,522ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 391877370,
            "unit": "rlimit",
            "extra": "smt-run=146,859ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 86989432,
            "unit": "rlimit",
            "extra": "smt-run=27,161ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 70123207,
            "unit": "rlimit",
            "extra": "smt-run=28,449ms"
          },
          {
            "name": "rlimit: arithmetic::internals::div_internals",
            "value": 13249888,
            "unit": "rlimit",
            "extra": "smt-run=1,733ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,654ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,690ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,181ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=858ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=656ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "15e0bb714754eff837723b53e777ac61f611d4c1",
          "message": "chore: fix `PartialSpec` for `Frame` (#768)\n\n* chore: fix `PartialSpec` for `Frame`\n\n* fmt",
          "timestamp": "2026-09-15T15:49:51+08:00",
          "tree_id": "7da884818571b613015f9e98bf6d9c25e52a9124",
          "url": "https://github.com/asterinas/vostd/commit/15e0bb714754eff837723b53e777ac61f611d4c1"
        },
        "date": 1789459279160,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1059198343,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=378,077ms wall=241,384ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 391762755,
            "unit": "rlimit",
            "extra": "smt-run=159,662ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 86989432,
            "unit": "rlimit",
            "extra": "smt-run=31,730ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 70123207,
            "unit": "rlimit",
            "extra": "smt-run=32,066ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,851ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,642ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,923ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,209ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=885ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=667ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "56c7f3f06757e2f9a64e1f433d4fc1f8f1150e8a",
          "message": "refactor: rebase `Atomicdatawithowner` and `OnceImpl` on `ResourceInvariant` (#769)\n\n* refactor `AtomicDataWithOwner`\n\n* refactor: rebase `AtomicDataWithOwner` with `ResourceInvariant``\n\n* rebase `OnceImpl`\n\n* fix comment",
          "timestamp": "2026-09-16T12:30:09+08:00",
          "tree_id": "6a8d33be7186a35287a5ec1554d4bfba3cc12342",
          "url": "https://github.com/asterinas/vostd/commit/56c7f3f06757e2f9a64e1f433d4fc1f8f1150e8a"
        },
        "date": 1789533744889,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1059105349,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=343,706ms wall=226,566ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 391762755,
            "unit": "rlimit",
            "extra": "smt-run=150,452ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 86989432,
            "unit": "rlimit",
            "extra": "smt-run=28,067ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 70123207,
            "unit": "rlimit",
            "extra": "smt-run=29,919ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,352ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,397ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,690ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,108ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=798ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=573ms"
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
          "id": "04aaba355673148e73ab0cc0329a20ad36291e8f",
          "message": "ci: skip jobs on cancelled runs (#771)",
          "timestamp": "2026-09-16T13:00:46+08:00",
          "tree_id": "82d46175e55293d880e4789b2433cc7553114e9c",
          "url": "https://github.com/asterinas/vostd/commit/04aaba355673148e73ab0cc0329a20ad36291e8f"
        },
        "date": 1789535156485,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1059105349,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=351,944ms wall=224,472ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 391762755,
            "unit": "rlimit",
            "extra": "smt-run=152,539ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 86989432,
            "unit": "rlimit",
            "extra": "smt-run=29,378ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 70123207,
            "unit": "rlimit",
            "extra": "smt-run=33,043ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,452ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,370ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,612ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,172ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=890ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=680ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "21346a50eed0fca06358d77da012c8c09c5ce9d4",
          "message": "fix: simplify `Range::clone` spec (#772)",
          "timestamp": "2026-09-16T15:37:34+08:00",
          "tree_id": "9250bad2a916ce9cfa5f6ebaac83a5ef63a866ba",
          "url": "https://github.com/asterinas/vostd/commit/21346a50eed0fca06358d77da012c8c09c5ce9d4"
        },
        "date": 1789544614091,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1079211122,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=351,714ms wall=226,391ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 391762755,
            "unit": "rlimit",
            "extra": "smt-run=150,785ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 86989432,
            "unit": "rlimit",
            "extra": "smt-run=24,030ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 70123207,
            "unit": "rlimit",
            "extra": "smt-run=33,582ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,438ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,415ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,742ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,183ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=862ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=630ms"
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
          "id": "9cec4bee109bcda2971f8f3b9e1d6c321892a49e",
          "message": "docs(coding-guidelines): add avoid-redundant-as-int-casts guideline (#773)\n\n* docs(coding-guidelines): add avoid-redundant-as-int-casts guideline\n\n* refine",
          "timestamp": "2026-09-16T20:18:49+08:00",
          "tree_id": "9fdf87f8b9b8996d5c3cc477545c3c512db19bfe",
          "url": "https://github.com/asterinas/vostd/commit/9cec4bee109bcda2971f8f3b9e1d6c321892a49e"
        },
        "date": 1789561617874,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1079211122,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=369,402ms wall=241,359ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 391762755,
            "unit": "rlimit",
            "extra": "smt-run=155,529ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 86989432,
            "unit": "rlimit",
            "extra": "smt-run=26,807ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 70123207,
            "unit": "rlimit",
            "extra": "smt-run=34,529ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,441ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,429ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,638ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,153ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=845ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=646ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "etyyuiope@qq.com",
            "name": "Hiroki Chen",
            "username": "hiroki-chen"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "a7a57fabff88ca077f7303cdecbcab7a2639feb0",
          "message": "Fix irc11 verus upgrade (#774)\n\n* Refresh IRC11 patches for the updated Verus toolchain\n\nPin IRC11 to Asterinas Verus fb2386ecea5a45810420577de3e312ded4f84b12,\nmatching the current default CI toolchain. Refresh the patch context for\nthe btree_cursors and no_trait_conflicts additions upstream; all added\nand removed implementation lines in the IRC11 patch remain unchanged.\n\nThis fixes bootstrap failures when applying the patch to vstd.rs and\nvstd_build/src/main.rs. The existing vstd compatibility patch still\napplies without changes, and the mainline Cargo.lock remains current.\n\nValidation: clean patch application, IRC11 bootstrap (2041 proofs),\nSC/IRC11 atomic smoke test, and vstd_extra verification (604 proofs).\n\n* Mark DMA and RCU monitor owners as objective\n\nThe ResourceInvariant refactor requires the resource of each\nSimpleResourceInvariant to implement Objective in IRC11 builds.\nAdd explicit implementations for the DMA and RCU monitor owners that\notherwise fail the Verus trait conflict checker.\n\nThe two DMA inner owners contain only PhantomData; the mapping set and\nRCU monitor owners are empty. These types carry no subjective memory\npermissions. Keep the implementations behind the irc11 feature.\n\nValidation: full IRC11 OSTD verification (1493 proofs), default make\n(1480 OSTD proofs), targeted verusfmt checks, and git diff --check.",
          "timestamp": "2026-09-16T16:47:48-04:00",
          "tree_id": "d3e7de3b3e6b4f838e33354438065483007a4c88",
          "url": "https://github.com/asterinas/vostd/commit/a7a57fabff88ca077f7303cdecbcab7a2639feb0"
        },
        "date": 1789592023771,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1079211122,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=340,524ms wall=222,697ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 391762755,
            "unit": "rlimit",
            "extra": "smt-run=146,456ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 86989432,
            "unit": "rlimit",
            "extra": "smt-run=29,752ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 70123207,
            "unit": "rlimit",
            "extra": "smt-run=30,570ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,233ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,361ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,606ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,094ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=866ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=573ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f1cb1247324ac8da185f4bd9349327b4bbf1ef57",
          "message": "remove unused ostd/specs/mm/vm_space_embedding.rs (#777)\n\nCo-authored-by: Je5s1e <chaoccc22@gmail.com>",
          "timestamp": "2026-09-17T11:39:41+08:00",
          "tree_id": "e615232c93922ae3d2327f9690f85a893eeaad38",
          "url": "https://github.com/asterinas/vostd/commit/f1cb1247324ac8da185f4bd9349327b4bbf1ef57"
        },
        "date": 1789617260444,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1160759419,
            "unit": "rlimit",
            "extra": "verified=4048 errors=0 smt-run=366,808ms wall=231,512ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 457151491,
            "unit": "rlimit",
            "extra": "smt-run=164,159ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80175175,
            "unit": "rlimit",
            "extra": "smt-run=26,805ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 53822410,
            "unit": "rlimit",
            "extra": "smt-run=26,053ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,513ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,412ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,775ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,197ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2004845,
            "unit": "rlimit",
            "extra": "smt-run=919ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=619ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1ab309964023b9383ae192284a6a032e614ac5c1",
          "message": "add inline description in guideline (#779)\n\nCo-authored-by: Je5s1e <chaoccc22@gmail.com>",
          "timestamp": "2026-09-17T15:28:26+08:00",
          "tree_id": "1b0357b88ca2957dc89566d3f30360b3c3f9d1ee",
          "url": "https://github.com/asterinas/vostd/commit/1ab309964023b9383ae192284a6a032e614ac5c1"
        },
        "date": 1789630562898,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1156124867,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=257,902ms wall=171,572ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 450627104,
            "unit": "rlimit",
            "extra": "smt-run=118,105ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80175175,
            "unit": "rlimit",
            "extra": "smt-run=20,138ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 66503652,
            "unit": "rlimit",
            "extra": "smt-run=17,499ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,599ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,027ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,123ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=840ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=587ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=408ms"
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
          "id": "cf3be3cd8ce55aa06fecb0381b769f9929956c03",
          "message": "refactor: move ostd-pod to ostd/libs (#780)",
          "timestamp": "2026-09-17T15:53:42+08:00",
          "tree_id": "55438225983b074a2353b36c930ffe9aafedf51b",
          "url": "https://github.com/asterinas/vostd/commit/cf3be3cd8ce55aa06fecb0381b769f9929956c03"
        },
        "date": 1789632086844,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1156124867,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=373,060ms wall=235,749ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 450627104,
            "unit": "rlimit",
            "extra": "smt-run=165,131ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80175175,
            "unit": "rlimit",
            "extra": "smt-run=29,283ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 53822410,
            "unit": "rlimit",
            "extra": "smt-run=25,816ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,757ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,474ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,744ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,192ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=969ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=688ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6e951a6f7bfe048fa9ba79971b388ae012902468",
          "message": "refactor: Add `FrameRawPerms` and refactor `Segment` perms (#781)\n\n* fix: Add `FrameRawPerms`\n\n* fix: `Frame::from_raw`\n\n* refactor: `Segment` permission\n\n* Minor\n\n* minor\n\n* Minor simplify\n\n* remove an unused spec fn\n\n* Minor",
          "timestamp": "2026-09-17T18:16:29+08:00",
          "tree_id": "cbeeba4ea74a78e6b3cff3de83490e3339d20a26",
          "url": "https://github.com/asterinas/vostd/commit/6e951a6f7bfe048fa9ba79971b388ae012902468"
        },
        "date": 1789640490430,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1107963611,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=231,399ms wall=159,791ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 331983855,
            "unit": "rlimit",
            "extra": "smt-run=89,614ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 107410625,
            "unit": "rlimit",
            "extra": "smt-run=24,393ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 76048027,
            "unit": "rlimit",
            "extra": "smt-run=16,936ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,623ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=943ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,122ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=826ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=564ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=408ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d08c320be8c7951d14f76ce295579abe69a387da",
          "message": "fix: `Segment::from_raw` (#783)",
          "timestamp": "2026-09-18T11:32:20+08:00",
          "tree_id": "92768e1fcb9124ca7ab8d099b9c7970d8f6ec083",
          "url": "https://github.com/asterinas/vostd/commit/d08c320be8c7951d14f76ce295579abe69a387da"
        },
        "date": 1789703160673,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1039710796,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=347,277ms wall=227,266ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 331983855,
            "unit": "rlimit",
            "extra": "smt-run=134,461ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 107410625,
            "unit": "rlimit",
            "extra": "smt-run=41,781ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 76048027,
            "unit": "rlimit",
            "extra": "smt-run=26,245ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,638ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,607ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,778ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,180ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=903ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=684ms"
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
          "id": "809bdffe8c9605d86431dd7c59aabdb76fc46bba",
          "message": "docs(coding-guidelines): update proof engineering and maintainability guidelines (#784)",
          "timestamp": "2026-09-18T13:27:48+08:00",
          "tree_id": "96167326c9c170ec64b09ce1e690537c21fce601",
          "url": "https://github.com/asterinas/vostd/commit/809bdffe8c9605d86431dd7c59aabdb76fc46bba"
        },
        "date": 1789709539393,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1039710796,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=272,629ms wall=182,883ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 331983855,
            "unit": "rlimit",
            "extra": "smt-run=111,076ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 107410625,
            "unit": "rlimit",
            "extra": "smt-run=32,858ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 76048027,
            "unit": "rlimit",
            "extra": "smt-run=18,709ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=1,862ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,048ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,305ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=929ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=626ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=456ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "dd7a8862017ee02a28e0543a1ecc35c8f697eb86",
          "message": "chore: use `proof_with` struct constructor when possible (#785)",
          "timestamp": "2026-09-18T15:20:44+08:00",
          "tree_id": "d70ee600f825ef4b9c92b113295e35081624ef62",
          "url": "https://github.com/asterinas/vostd/commit/dd7a8862017ee02a28e0543a1ecc35c8f697eb86"
        },
        "date": 1789716439508,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1039710796,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=338,334ms wall=217,481ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 331983855,
            "unit": "rlimit",
            "extra": "smt-run=132,373ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 107410625,
            "unit": "rlimit",
            "extra": "smt-run=37,132ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 76048027,
            "unit": "rlimit",
            "extra": "smt-run=28,165ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,485ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,446ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,723ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,158ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=895ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=660ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "69f005898d5d203bc59c9e7ffd8428be608222c2",
          "message": "prove: boot::memory_region::Deref (#782)\n\n* prove: boot::memory_region::Deref\n\n* Remove redundant MemoryRegionArray Inv implementation\n\n* Remove redundant MemoryRegionArray invariant\n\n* simplify postcondition of deref\n\n---------\n\nCo-authored-by: Je5s1e <chaoccc22@gmail.com>",
          "timestamp": "2026-09-18T16:08:09+08:00",
          "tree_id": "48308f006a21e225cc720434360a5275fa7860cf",
          "url": "https://github.com/asterinas/vostd/commit/69f005898d5d203bc59c9e7ffd8428be608222c2"
        },
        "date": 1789719786997,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1039768479,
            "unit": "rlimit",
            "extra": "verified=4050 errors=0 smt-run=336,987ms wall=219,057ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 331983855,
            "unit": "rlimit",
            "extra": "smt-run=131,335ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 107410625,
            "unit": "rlimit",
            "extra": "smt-run=42,775ms"
          },
          {
            "name": "rlimit: specs::mm::embedding",
            "value": 48459213,
            "unit": "rlimit",
            "extra": "smt-run=22,203ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9455652,
            "unit": "rlimit",
            "extra": "smt-run=2,505ms"
          },
          {
            "name": "rlimit: endian",
            "value": 8889145,
            "unit": "rlimit",
            "extra": "smt-run=1,367ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 5154488,
            "unit": "rlimit",
            "extra": "smt-run=1,748ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3716957,
            "unit": "rlimit",
            "extra": "smt-run=1,140ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1990774,
            "unit": "rlimit",
            "extra": "smt-run=939ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1499192,
            "unit": "rlimit",
            "extra": "smt-run=658ms"
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
          "id": "676d998d57618c26fde6a9de3c7a0e73bae8ebef",
          "message": "ci: parallelize doc build (#786)\n\n* ci: parallelize doc build\n\n* ci: remove pr-comment-verify\n\n* ci: fix",
          "timestamp": "2026-09-18T12:46:09Z",
          "tree_id": "07a309d74ab154ea68bb443896eb6c4dc67a9606",
          "url": "https://github.com/asterinas/vostd/commit/676d998d57618c26fde6a9de3c7a0e73bae8ebef"
        },
        "date": 1789735869000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1039768479,
            "extra": "verified=4050 errors=0 smt-run=360,332ms wall=231,976ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 331983855,
            "extra": "smt-run=139,766ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 107410625,
            "extra": "smt-run=46,010ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 76048027,
            "extra": "smt-run=30,579ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9455652,
            "extra": "smt-run=2,648ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 8889145,
            "extra": "smt-run=1,498ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 5154488,
            "extra": "smt-run=1,755ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,260ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1990774,
            "extra": "smt-run=878ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=655ms"
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
          "id": "74cdb40bb5ccbb0c5ccb5f98bf29af3bd1fe774b",
          "message": "prove: boot::memory_region::as_aligned (#778)\n\n* prove: boot::memory_region::as_aligned\n\n* refine: remove MemRegionModel\n\n* refine: review skill\n\n* refine: view MemoryRegionArray as Seq<MemoryRegion>",
          "timestamp": "2026-09-19T11:19:53Z",
          "tree_id": "3f2d832499ce7793085a857da8dfdaf8e687294b",
          "url": "https://github.com/asterinas/vostd/commit/74cdb40bb5ccbb0c5ccb5f98bf29af3bd1fe774b"
        },
        "date": 1789817507000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1039896275,
            "extra": "verified=4050 errors=0 smt-run=355,995ms wall=229,196ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 331983855,
            "extra": "smt-run=137,104ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 107410625,
            "extra": "smt-run=43,509ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 76048027,
            "extra": "smt-run=26,675ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9455652,
            "extra": "smt-run=2,603ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 8889145,
            "extra": "smt-run=1,537ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 5154488,
            "extra": "smt-run=1,735ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,210ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1990774,
            "extra": "smt-run=940ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=692ms"
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
          "id": "ec90b55261de088c5d85b69441c48c23a651507b",
          "message": "prove(ostd-pod): add from_bytes back and sync with mainline (#787)",
          "timestamp": "2026-09-20T03:01:39Z",
          "tree_id": "7adfcbd08008e346d7ed215b3c7b7da56ac20817",
          "url": "https://github.com/asterinas/vostd/commit/ec90b55261de088c5d85b69441c48c23a651507b"
        },
        "date": 1789874128000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1039116753,
            "extra": "verified=4050 errors=0 smt-run=338,735ms wall=219,333ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 331983855,
            "extra": "smt-run=131,476ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 107410625,
            "extra": "smt-run=39,557ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 76048027,
            "extra": "smt-run=28,807ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9455652,
            "extra": "smt-run=2,575ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 8889145,
            "extra": "smt-run=1,464ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 5154488,
            "extra": "smt-run=1,668ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,154ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1990774,
            "extra": "smt-run=977ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=643ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f34c1d1f3bc895ae6da2097157caf18bc792dc7c",
          "message": "fix `Frame::clone` (#788)",
          "timestamp": "2026-09-20T03:46:21Z",
          "tree_id": "62d544d5b0da5dbd2f60a0f3d32edf4e2dbd19a6",
          "url": "https://github.com/asterinas/vostd/commit/f34c1d1f3bc895ae6da2097157caf18bc792dc7c"
        },
        "date": 1789876742000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1098631420,
            "extra": "verified=4050 errors=0 smt-run=363,825ms wall=231,090ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345942219,
            "extra": "smt-run=139,239ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 108057253,
            "extra": "smt-run=43,241ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 70566556,
            "extra": "smt-run=27,842ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,545ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,392ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,578ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,171ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=916ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=640ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d4ca0f50020910932ec41a8a54ff3e6d21a9717f",
          "message": "chore: new subrange syntax (#790)\n\n* chore: new subrange syntax\n\n* Update ci-irc11.yml\n\n* Revert \"Update ci-irc11.yml\"\n\nThis reverts commit 759a52d9fd5a21d5a7fa13170340175ae87a26ba.",
          "timestamp": "2026-09-20T05:58:50Z",
          "tree_id": "0b1eba906cc66222194cf162341f47e275170ca0",
          "url": "https://github.com/asterinas/vostd/commit/d4ca0f50020910932ec41a8a54ff3e6d21a9717f"
        },
        "date": 1789884180000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1028502202,
            "extra": "verified=4050 errors=0 smt-run=266,528ms wall=177,601ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345942219,
            "extra": "smt-run=103,436ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 108057253,
            "extra": "smt-run=28,696ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 76632331,
            "extra": "smt-run=23,504ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,112ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,700ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,088ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=863ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=619ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=440ms"
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
          "id": "2e380c9e4eeb9f68d874067e4711d3f11962007c",
          "message": "prove: cpu::set (#770)\n\n* prove: add smallvec spec\n\n* prove: cpu::set\n\n* simplify\n\n* chore: comment for usize::div_ceil\n\n* WIP: prove set::set by rewriting\n\n* refine\n\n* refine: review skill\n\n* refine: return in assume_specification\n\n* refine: update CpuId to use int instead of u32 and adjust related specifications\n\n* refine: xinyi\n\n* refine: `when_used_as_spec`\n\n* refine: external_body for num_cpus\n\n* sync: Cargo.lock\n\n* refine\n\n* fmt\n\n* refine: lemma_u64_zero_and_bit to lemma_u64_and_zero\n\n* refine: move lemmas into the end of the file\n\n* chore\n\n* refine: subrange\n\n* refine: private and restore\n\n* refine: review skill\n\n* refine: remove pub, and add more specs for smallvec\n\n* refine: review skill\n\n* simplify: cpu::set\n\n* refine: extract u64_bit_is_set spec fn in vstd_extra by macro\n\n* refine: generalize bit lemmas and simplify set-bit counting\n\n* new subrange syntax and change names\n\n* use dual_spec\n\n* minor\n\n---------\n\nCo-authored-by: rikosellic <64517311+rikosellic@users.noreply.github.com>",
          "timestamp": "2026-09-20T07:30:09Z",
          "tree_id": "ca544e240d522d707376225fdad527b6c69697db",
          "url": "https://github.com/asterinas/vostd/commit/2e380c9e4eeb9f68d874067e4711d3f11962007c"
        },
        "date": 1789890624000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1034802236,
            "extra": "verified=4231 errors=0 smt-run=262,744ms wall=177,694ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345942219,
            "extra": "smt-run=104,144ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 115339830,
            "extra": "smt-run=21,852ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 108057253,
            "extra": "smt-run=27,868ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,102ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,734ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,093ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=871ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=647ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=459ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6f7c7c1293f5c256fa1290f86201cf7a17d2b90d",
          "message": "chore: reorder import (#792)\n\n* chore: reorder imports\n\n* fmt\n\n* remove blank line between `vstd` and `vstd_extra`",
          "timestamp": "2026-09-20T08:08:59Z",
          "tree_id": "e2f72effa2f8737e3494f6087257c5cdecf8ea0f",
          "url": "https://github.com/asterinas/vostd/commit/6f7c7c1293f5c256fa1290f86201cf7a17d2b90d"
        },
        "date": 1789892036000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1034802236,
            "extra": "verified=4231 errors=0 smt-run=360,161ms wall=232,584ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345942219,
            "extra": "smt-run=142,820ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 108057253,
            "extra": "smt-run=36,458ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 74419027,
            "extra": "smt-run=27,803ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,542ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,330ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,722ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,190ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=919ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=647ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6bc6c7fd3c0a402e35d30f01518e7d3516c59da6",
          "message": "prove: `Segment::from<Frame>` (#793)",
          "timestamp": "2026-09-20T08:44:02Z",
          "tree_id": "66a28c6937b3a4250cd5b9ea1aed03060961a795",
          "url": "https://github.com/asterinas/vostd/commit/6bc6c7fd3c0a402e35d30f01518e7d3516c59da6"
        },
        "date": 1789894189000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1031773933,
            "extra": "verified=4232 errors=0 smt-run=271,530ms wall=183,375ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345942219,
            "extra": "smt-run=108,665ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 115339830,
            "extra": "smt-run=23,244ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 108057253,
            "extra": "smt-run=31,127ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,076ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,636ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,111ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=859ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=628ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=447ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "880b27f667701bd27e1817b5cedc2598f357a979",
          "message": "chore: some small fixes (#794)\n\n* chore: use `dual_spec`\n\n* remove `CpuSet` in `specs`\n\n* fix: `CpuSet` import\n\n* chore: remove some `as int`\n\n* chore: remove more `as int`",
          "timestamp": "2026-09-20T09:46:34Z",
          "tree_id": "f128c939066e1c2cd0ac22e2027af03f6891eefa",
          "url": "https://github.com/asterinas/vostd/commit/880b27f667701bd27e1817b5cedc2598f357a979"
        },
        "date": 1789897923000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1030919038,
            "extra": "verified=4232 errors=0 smt-run=210,599ms wall=146,262ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345942219,
            "extra": "smt-run=86,848ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 115339830,
            "extra": "smt-run=17,104ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 108057253,
            "extra": "smt-run=23,994ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=824ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,254ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=818ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=673ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2025856,
            "extra": "smt-run=339ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=481ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d73d234f3d5a5b1b1519ff25e45e3864c6f7353b",
          "message": "chore: Some cleanup and renaming (#795)\n\n* choreL rename `meta_vaddr` to `slot_vaddr`\n\n* cleanup",
          "timestamp": "2026-09-21T03:37:17Z",
          "tree_id": "608287a39a593342724e9ab763108f8bca3f9eef",
          "url": "https://github.com/asterinas/vostd/commit/d73d234f3d5a5b1b1519ff25e45e3864c6f7353b"
        },
        "date": 1789962538000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1030919156,
            "extra": "verified=4232 errors=0 smt-run=378,507ms wall=241,915ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345942219,
            "extra": "smt-run=148,408ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 115339830,
            "extra": "smt-run=30,891ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 108057253,
            "extra": "smt-run=42,329ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,533ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,429ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,722ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,269ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=968ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=693ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1f190f741f8856fb90a96e2810ae996323b5d7cb",
          "message": "fix: partly fix `NonNullPtr` for `Frame` (#798)",
          "timestamp": "2026-09-21T06:47:11Z",
          "tree_id": "b8c81bc571fa7045185c7ffbc538d238b659ccda",
          "url": "https://github.com/asterinas/vostd/commit/1f190f741f8856fb90a96e2810ae996323b5d7cb"
        },
        "date": 1789973527000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1001835886,
            "extra": "verified=4231 errors=0 smt-run=261,040ms wall=179,597ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 358168337,
            "extra": "smt-run=113,987ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 115339833,
            "extra": "smt-run=20,360ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 63003025,
            "extra": "smt-run=19,766ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,151ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,671ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=979ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=867ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=642ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=468ms"
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
          "id": "e90faae127d587448c5b7778a3f14c457fb24f9e",
          "message": "docs(coding-guidelines): import layout, trivial-contract exemption, and so on (#799)\n\n* docs(coding-guidelines): import layout, trivial-contract exemption, PR #770 lessons\n\n* chore: reorder imports to the verification-groups layout\n\n* refine: add `dual_spec`\n\n* refine: group lay-out-the-import-section and group-imports-by-crate again",
          "timestamp": "2026-09-21T08:52:44Z",
          "tree_id": "b92d9b9cd52885c5b9c5304ff7c2f82fccee1b92",
          "url": "https://github.com/asterinas/vostd/commit/e90faae127d587448c5b7778a3f14c457fb24f9e"
        },
        "date": 1789981084000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1001835886,
            "extra": "verified=4231 errors=0 smt-run=339,897ms wall=221,326ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 358168337,
            "extra": "smt-run=139,712ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 115339833,
            "extra": "smt-run=30,949ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 63003025,
            "extra": "smt-run=27,482ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,524ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,355ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,527ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,164ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=934ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=641ms"
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
          "id": "25f07075f88e3acf82c42d736f270efccbfff005",
          "message": "doc(guidelines): Origin Rust markers, Seq sugar conversion, and fmt policy (#800)\n\n* docs(coding-guidelines): add seq range slicing guideline\n\n* docs(coding-guidelines): require origin rust comments for exec rewrites\n\n* refactor(specs): replace take/skip with slice syntax in linked list specs\n\n* docs(coding-guidelines): update verusfmt guidance for range forms\n\n* fix\n\n* fmt",
          "timestamp": "2026-09-22T12:46:22Z",
          "tree_id": "141651e92c15a549eb8677511566513de1d0a283",
          "url": "https://github.com/asterinas/vostd/commit/25f07075f88e3acf82c42d736f270efccbfff005"
        },
        "date": 1790082146000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1078317798,
            "extra": "verified=4231 errors=0 smt-run=359,908ms wall=231,785ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 358168337,
            "extra": "smt-run=146,050ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 191991283,
            "extra": "smt-run=42,339ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 76943258,
            "extra": "smt-run=26,769ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,558ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,526ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,515ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,184ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=940ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=633ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "etyyuiope@qq.com",
            "name": "Hiroki Chen",
            "username": "hiroki-chen"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "88bb87d920063dcaba6acfeb27e763029b818c14",
          "message": "Restore IRC11 verification after mainline updates (#801)\n\nAdvance the pinned Asterinas Verus revision to 486d4f1728731cd918f5dbb6c39feef756b42c91,\nthe upstream main revision checked on 2026-09-22. It supports the Seq range\nsyntax now used by VOSTD and matches the mainline Cargo.lock versions.\nBoth existing IRC11 patches apply unchanged.\n\nUpdate the IRC11 scheduler imports after CpuId moved to crate::cpu, resolve\nObjective in Frame's NonNullPtr contract, and mark FrameRawPerms objective.\nThe latter contains only slot points-to and counted metadata permissions;\nit carries no subjective weak-memory observations. Runtime bodies and\nexisting contracts are unchanged.\n\nValidation: IRC11 bootstrap and atomic smoke test; vstd_extra 746 verified;\nIRC11 OSTD 1534 verified; default make OSTD 1521 verified; all zero errors.\nChanged Rust files pass verusfmt --edition 2024 --check and git diff --check.",
          "timestamp": "2026-09-23T18:08:14Z",
          "tree_id": "ab9a8eb16522e18c69644ffccf54d3ee3ccacc41",
          "url": "https://github.com/asterinas/vostd/commit/88bb87d920063dcaba6acfeb27e763029b818c14"
        },
        "date": 1790187627000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1078317798,
            "extra": "verified=4231 errors=0 smt-run=354,977ms wall=228,611ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 358168337,
            "extra": "smt-run=147,889ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 191991283,
            "extra": "smt-run=34,668ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 63003025,
            "extra": "smt-run=26,347ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,501ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,400ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,454ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,159ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=914ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=668ms"
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
          "id": "bdfd6e17f7b36979386461e82bacb719f065ed6f",
          "message": "simplify: specs::mm::embedding::list_store (#806)",
          "timestamp": "2026-09-24T05:59:50Z",
          "tree_id": "d758a28c83d721bc4cde1a085b1ed9d62ffb0954",
          "url": "https://github.com/asterinas/vostd/commit/bdfd6e17f7b36979386461e82bacb719f065ed6f"
        },
        "date": 1790230159000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1015104297,
            "extra": "verified=4228 errors=0 smt-run=369,939ms wall=239,138ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 329313601,
            "extra": "smt-run=154,832ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 191991283,
            "extra": "smt-run=46,753ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 70530342,
            "extra": "smt-run=27,661ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,520ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,517ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,604ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,382ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=1,056ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=710ms"
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
          "id": "8f7195499b08f582531c75aaa3440063d533db7a",
          "message": "simplify: specs::mm::page_table::{mod, cursor::{owners, mapping_set_lemmas}} (#807)\n\n* simplify: specs::mm::page_table\n\n* simplify: specs::mm::page_table::cursor::mapping_set_lemmas\n\n* simplify: specs::mm::page_table::cursor::owners",
          "timestamp": "2026-09-25T02:05:10Z",
          "tree_id": "75c19d6ec08c28ae3791e7d345d818bc2da9e7b9",
          "url": "https://github.com/asterinas/vostd/commit/8f7195499b08f582531c75aaa3440063d533db7a"
        },
        "date": 1790302212000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1018915524,
            "extra": "verified=4214 errors=0 smt-run=317,063ms wall=219,292ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 329313655,
            "extra": "smt-run=128,676ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 191991283,
            "extra": "smt-run=40,398ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 64029421,
            "extra": "smt-run=26,725ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,420ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,216ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,318ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,116ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2025856,
            "extra": "smt-run=549ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=821ms"
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
          "id": "6e685444b8bcce9dd1823d53bcda6f98eb9e7b05",
          "message": "fmt: update to verusfmt 0.7.4 (#808)\n\n* fmt: update to verusfmt 0.7.4\n\n* docs(coding-guidelines): clarify spec file size threshold\n\n* docs(coding-guidelines): specify verified properties section format",
          "timestamp": "2026-09-26T15:02:24Z",
          "tree_id": "f5644c77dec118b21c14021c1d78bf78529c515f",
          "url": "https://github.com/asterinas/vostd/commit/6e685444b8bcce9dd1823d53bcda6f98eb9e7b05"
        },
        "date": 1790435277000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1018915524,
            "extra": "verified=4214 errors=0 smt-run=339,749ms wall=222,803ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 329313655,
            "extra": "smt-run=137,790ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 191991283,
            "extra": "smt-run=39,055ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 64029421,
            "extra": "smt-run=26,640ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,613ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,371ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,646ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,209ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=992ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=701ms"
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
          "id": "7321dfb65e2c0f63b87ae249221f1af5d70fcc05",
          "message": "prove: AtomicCpuSet (#796)",
          "timestamp": "2026-09-28T07:39:13Z",
          "tree_id": "7ab858dd997ee352635eff8c612628c04a628448",
          "url": "https://github.com/asterinas/vostd/commit/7321dfb65e2c0f63b87ae249221f1af5d70fcc05"
        },
        "date": 1790581431000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1032068436,
            "extra": "verified=4223 errors=0 smt-run=267,854ms wall=183,266ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 329313655,
            "extra": "smt-run=105,637ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 191991283,
            "extra": "smt-run=37,360ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 64029421,
            "extra": "smt-run=22,768ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,134ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,745ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,113ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=909ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=665ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=474ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "bd9a25ddace74af5b0529f3ed4d005fe0bd1705d",
          "message": "chore: remove reundant `spec fn` and `proof fn` (#810)\n\n* clear comments\n\n* minor\n\n* delete unused lemmas\n\n* delete more\n\n* clear comment\n\n* delete more\n\n* delete more\n\n* delete more",
          "timestamp": "2026-09-28T08:56:38Z",
          "tree_id": "dd7a0094cb5dd310bdb2756bb28a724f7fe738be",
          "url": "https://github.com/asterinas/vostd/commit/bd9a25ddace74af5b0529f3ed4d005fe0bd1705d"
        },
        "date": 1790586124000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1029441972,
            "extra": "verified=4197 errors=0 smt-run=311,066ms wall=206,095ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 329313656,
            "extra": "smt-run=122,417ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 192028366,
            "extra": "smt-run=38,441ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 75213460,
            "extra": "smt-run=26,409ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,516ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=2,374ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,631ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,147ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=931ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=624ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "etyyuiope@qq.com",
            "name": "Hiroki Chen",
            "username": "hiroki-chen"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c4a8824eed1745bb1aad6331ac53cc0a48158d6f",
          "message": "Move generic RCU object resources to vstd_extra (#804)\n\nKeep the allocation registry, typed block identity, base retire permission, and client-owned object wrapper together in the reusable proof library. OSTD now retains only its root publication history and imports the generic resources.\n\nVerified with default and IRC11 toolchains: vstd_extra (734/757) and ostd (1478/1491), all with zero errors.",
          "timestamp": "2026-09-28T18:31:16Z",
          "tree_id": "42da59fff41de02a2f65435e60e46448643fb0ee",
          "url": "https://github.com/asterinas/vostd/commit/c4a8824eed1745bb1aad6331ac53cc0a48158d6f"
        },
        "date": 1790620599000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1029460290,
            "extra": "verified=4199 errors=0 smt-run=259,258ms wall=178,706ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 329313656,
            "extra": "smt-run=109,628ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 192028366,
            "extra": "smt-run=31,288ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 75213460,
            "extra": "smt-run=20,978ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,109ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,610ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,121ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=862ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2025856,
            "extra": "smt-run=448ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=676ms"
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
          "id": "fd133bccf8f67d659b09d299c6575867bbd06271",
          "message": "prove: range allocator state tracking (#809)\n\n* prove: range allocator state tracking\n\n* manually simplify\n\n* minor\n\n---------\n\nCo-authored-by: rikosellic <64517311+rikosellic@users.noreply.github.com>",
          "timestamp": "2026-09-29T06:43:18Z",
          "tree_id": "8db50a6f8f64b902e49f54a6f4487a690a3a09fd",
          "url": "https://github.com/asterinas/vostd/commit/fd133bccf8f67d659b09d299c6575867bbd06271"
        },
        "date": 1790664571000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1029677639,
            "extra": "verified=4209 errors=0 smt-run=251,105ms wall=174,061ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 338125789,
            "extra": "smt-run=106,544ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 192028366,
            "extra": "smt-run=32,631ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 73925433,
            "extra": "smt-run=18,997ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,113ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8765644,
            "extra": "smt-run=1,734ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,100ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=867ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=666ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=474ms"
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
          "id": "f4d24bf6b6310ab65b69d24fa63b433247743148",
          "message": "sync: delegate fmt to `cargo verus fmt` (#813)",
          "timestamp": "2026-10-03T07:33:46Z",
          "tree_id": "283ed3a6ad306afa4df06b8c217f84a552f8aa47",
          "url": "https://github.com/asterinas/vostd/commit/f4d24bf6b6310ab65b69d24fa63b433247743148"
        },
        "date": 1791013590000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1182848609,
            "extra": "verified=4210 errors=0 smt-run=357,579ms wall=233,592ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 338125789,
            "extra": "smt-run=145,759ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 192028366,
            "extra": "smt-run=44,430ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 73925433,
            "extra": "smt-run=27,498ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,447ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8529093,
            "extra": "smt-run=2,068ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,453ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,152ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=829ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=585ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b529f0a23568e1f2a43291b879b1cb9d9cd7ad14",
          "message": "refactor: remove AbstractVAddr (#814)\n\n* Minor\n\n* remove legacy code\n\n* progress\n\n* progress\n\n* refactor\n\n* more refactor\n\n* refactor\n\n* more refactor\n\n* more refactor\n\n* more refactor\n\n* more refactor\n\n* fmt\n\n* remove a requirement\n\n* some renaming",
          "timestamp": "2026-10-08T01:47:50Z",
          "tree_id": "cf746b80990ae5bbc7d1f8e103976a19695ee1c8",
          "url": "https://github.com/asterinas/vostd/commit/b529f0a23568e1f2a43291b879b1cb9d9cd7ad14"
        },
        "date": 1791424830000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1130929208,
            "extra": "verified=4159 errors=0 smt-run=352,096ms wall=227,825ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 298388219,
            "extra": "smt-run=136,979ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 192028366,
            "extra": "smt-run=37,553ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 73046986,
            "extra": "smt-run=25,387ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 11447340,
            "extra": "smt-run=1,606ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8529093,
            "extra": "smt-run=2,337ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4381818,
            "extra": "smt-run=1,626ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3716957,
            "extra": "smt-run=1,230ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1994262,
            "extra": "smt-run=955ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1499192,
            "extra": "smt-run=684ms"
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
          "id": "1fecd7c0ca4446a819e184df41c78e8150cfed7c",
          "message": "ci: shall not continue on macOS error (#815)\n\n* ci: shall not continue on macOS error\n\n* chore: cargo.lock",
          "timestamp": "2026-10-08T07:26:20Z",
          "tree_id": "b5d43d735e1b3e4ce956f3695ddfc3ce1018d533",
          "url": "https://github.com/asterinas/vostd/commit/1fecd7c0ca4446a819e184df41c78e8150cfed7c"
        },
        "date": 1791445251000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 958838438,
            "extra": "verified=4159 errors=0 smt-run=209,698ms wall=147,698ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 319680062,
            "extra": "smt-run=87,309ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137742433,
            "extra": "smt-run=21,254ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 61449449,
            "extra": "smt-run=19,737ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=2,659ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=1,328ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,001ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=573ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2025856,
            "extra": "smt-run=365ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=460ms"
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
          "id": "ee5210d25f380dd50c83a4aa42125a77e7ddb129",
          "message": "ci: merge verus upstream pr-3104 (#816)",
          "timestamp": "2026-10-08T08:33:54Z",
          "tree_id": "1bed128694a1b773aa3151b1e736d9de441fc1f5",
          "url": "https://github.com/asterinas/vostd/commit/ee5210d25f380dd50c83a4aa42125a77e7ddb129"
        },
        "date": 1791448997000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 958838438,
            "extra": "verified=4159 errors=0 smt-run=344,925ms wall=230,143ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 319680062,
            "extra": "smt-run=140,977ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137742433,
            "extra": "smt-run=35,775ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 61449449,
            "extra": "smt-run=32,018ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=4,783ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,391ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,623ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=1,051ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=855ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=613ms"
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
          "id": "cfc343893bde3164cb2881b98f678b7abe9190c9",
          "message": "prove: arch/x86/kernel/acpi (#789)",
          "timestamp": "2026-10-08T09:07:18Z",
          "tree_id": "121c793428644dd1a58d0577b8c524cfe469be3d",
          "url": "https://github.com/asterinas/vostd/commit/cfc343893bde3164cb2881b98f678b7abe9190c9"
        },
        "date": 1791451110000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 955233368,
            "extra": "verified=4194 errors=0 smt-run=316,826ms wall=210,459ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 319680062,
            "extra": "smt-run=127,963ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137742433,
            "extra": "smt-run=30,681ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 61449449,
            "extra": "smt-run=27,223ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=4,713ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,541ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,729ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=988ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=836ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=609ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "de73f2ef2ccdbd8933e545e9cbc0f193ae1f43a4",
          "message": "Mut self (#817)\n\n* use mut self\n\n* Update ci-irc11.yml\n\n* Update verus-irc11-vstd.patch\n\n* Update verus-irc11-vstd.patch",
          "timestamp": "2026-10-08T11:37:22Z",
          "tree_id": "063f13370cf97ec1737c9d555051b95ed11d463e",
          "url": "https://github.com/asterinas/vostd/commit/de73f2ef2ccdbd8933e545e9cbc0f193ae1f43a4"
        },
        "date": 1791459761000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 956525292,
            "extra": "verified=4194 errors=0 smt-run=331,010ms wall=218,627ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 319680062,
            "extra": "smt-run=133,400ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137746526,
            "extra": "smt-run=31,876ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 61449449,
            "extra": "smt-run=27,046ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=4,965ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,467ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,794ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=1,032ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=899ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=617ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7e53bd1223e5c3f958c863ad48dcb917cd8e9b3e",
          "message": "fix (#818)",
          "timestamp": "2026-10-08T12:39:31Z",
          "tree_id": "e8d370f9177c58056627f7a97aca2b4cd2c32924",
          "url": "https://github.com/asterinas/vostd/commit/7e53bd1223e5c3f958c863ad48dcb917cd8e9b3e"
        },
        "date": 1791463489000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 956525292,
            "extra": "verified=4194 errors=0 smt-run=361,795ms wall=232,951ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 319680062,
            "extra": "smt-run=147,240ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137746526,
            "extra": "smt-run=32,907ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 61449449,
            "extra": "smt-run=34,576ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=5,037ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,580ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,796ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=1,089ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=912ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=667ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c1c860d25c2529eb8c7a9f2a4608b087878851eb",
          "message": "First step towards general arch: add `<C: PagingConstsTrait>` back to `page_size` (#821)\n\n* restore `page_size` trait bound\n\n* remove page_size_for_level_spec\n\n* simplify\n\n* fmt\n\n* f",
          "timestamp": "2026-10-09T08:41:53Z",
          "tree_id": "bcdd9d5abe80c287f1a4de0c777761a7852f2cff",
          "url": "https://github.com/asterinas/vostd/commit/c1c860d25c2529eb8c7a9f2a4608b087878851eb"
        },
        "date": 1791537957000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 936256164,
            "extra": "verified=4193 errors=0 smt-run=335,997ms wall=223,264ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 301399299,
            "extra": "smt-run=138,418ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137746526,
            "extra": "smt-run=31,446ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 53383304,
            "extra": "smt-run=25,264ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=4,818ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,620ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,730ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=1,045ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=926ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=627ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "49c4ebb1ef9d21be270c9475c42f76a89fec18bd",
          "message": "fix: add atomic precondtions (#822)\n\n* fix: add atomic precondtions\n\n* minor",
          "timestamp": "2026-10-10T03:26:55Z",
          "tree_id": "fcd1b37515d8011cb16efdcab77b53ed89412321",
          "url": "https://github.com/asterinas/vostd/commit/49c4ebb1ef9d21be270c9475c42f76a89fec18bd"
        },
        "date": 1791603182000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 936256873,
            "extra": "verified=4193 errors=0 smt-run=309,781ms wall=213,415ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 301399299,
            "extra": "smt-run=127,466ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137746526,
            "extra": "smt-run=31,363ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 62177235,
            "extra": "smt-run=21,874ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=4,540ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,207ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,392ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=979ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=820ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=574ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0de9219aa933a2bcc1176b9639412dc2efc30612",
          "message": "chore: generalize page size lemmas (#823)\n\n* chore: generalize page size lemmas\n\n* change some lemma names\n\n* change some comments",
          "timestamp": "2026-10-10T08:46:57Z",
          "tree_id": "948ce39257fca0478b93ffb3399b257d45aa118b",
          "url": "https://github.com/asterinas/vostd/commit/0de9219aa933a2bcc1176b9639412dc2efc30612"
        },
        "date": 1791625453000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 971320481,
            "extra": "verified=4188 errors=0 smt-run=347,402ms wall=224,755ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 335861703,
            "extra": "smt-run=151,545ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137746526,
            "extra": "smt-run=31,883ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 52658599,
            "extra": "smt-run=25,146ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=5,013ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,745ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,728ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=1,033ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=926ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=678ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "etyyuiope@qq.com",
            "name": "Hiroki Chen",
            "username": "hiroki-chen"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7d25cc5b27caa4fd8e8b0fc62ef4ee9376de0604",
          "message": "Rcu typed root (#824)\n\n* Retain typed identities in IRC11 root histories\n\nExtract the initial typed root state from the weak-memory prototype. Keep the latest registration and client resource linear while retaining persistent block information for every registered allocation.\n\nRelate each non-null native history message to its exact typed pointer, including provenance. Provide a lookup that duplicates only the identity metadata, so stale-message resolution supplies no memory-access or reclamation permission.\n\nValidation: default full verification (1523 OSTD proofs), full IRC11 OSTD verification (1538 proofs), targeted rustfmt/verusfmt, and git diff --check.\n\n* Add fresh typed RCU root publication transition\n\nAppend a fresh registration or null message to RcuRootOwnedGhost while preserving every historical typed identity. Return the previous current object as a linear resource and retain a fresh persistent identity for a new non-null publication.\n\nThis transition moves bookkeeping and client resources only; it does not establish detachment or permission to reclaim the previous allocation.\n\nValidation: default full verification (1523 OSTD proofs), full IRC11 OSTD verification (1539 proofs), targeted rustfmt/verusfmt, and git diff --check.\n\n* Add RCU paper",
          "timestamp": "2026-10-11T03:24:21Z",
          "tree_id": "64e0ce70e8ebb22b1d6ffd5a655f2a97c0ba9c08",
          "url": "https://github.com/asterinas/vostd/commit/7d25cc5b27caa4fd8e8b0fc62ef4ee9376de0604"
        },
        "date": 1791689803000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 971320481,
            "extra": "verified=4188 errors=0 smt-run=324,729ms wall=217,953ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 335861703,
            "extra": "smt-run=134,239ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137746526,
            "extra": "smt-run=30,547ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 52658599,
            "extra": "smt-run=26,452ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=4,749ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,118ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=994ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=816ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=592ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "unit": "rlimit",
            "value": 1451903,
            "extra": "smt-run=1,510ms"
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
          "id": "a53aaa589ee497c003f60015da1ee8005a68d0ef",
          "message": "prove: verify AtomicCpuId (#812)",
          "timestamp": "2026-10-11T09:31:51Z",
          "tree_id": "dfeda18b77ccfbec1a9094b3ea65327386abf661",
          "url": "https://github.com/asterinas/vostd/commit/a53aaa589ee497c003f60015da1ee8005a68d0ef"
        },
        "date": 1791711499000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 971637173,
            "extra": "verified=4197 errors=0 smt-run=333,790ms wall=219,282ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 335861703,
            "extra": "smt-run=140,315ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 137746526,
            "extra": "smt-run=28,648ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 52658599,
            "extra": "smt-run=27,518ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423851,
            "extra": "smt-run=4,786ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 8984043,
            "extra": "smt-run=2,585ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940707,
            "extra": "smt-run=1,695ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602266,
            "extra": "smt-run=1,016ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=921ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=642ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0d139e00d628e23257aa7ec60916df99867698a7",
          "message": "fix: optimize spec and proof fns (#827)\n\n* simplification\n\n* Create ostd-spec-optimization-review.md\n\n* remove redundant `lemma_meta_to_frame_alignment`\n\n* small fixes\n\n* small fixes\n\n* small fixes\n\n* small fixes\n\n* remove legacy entryview\n\n* small fixes\n\n* remove redundant spec fn\n\n* fix some page table lemmas\n\n* remove a duplicate proof\n\n* remove another redundant proof\n\n* remove redundant spec\n\n* small fixes\n\n* fixes\n\n* simplify a spec\n\n* remove redundant function\n\n* remove redundant proof\n\n* remove more redundant proof\n\n* simplify a spec fn implementation\n\n* simplify a spec fn\n\n* fix redundant proof\n\n* fix postcondition\n\n* simplify a proof\n\n* fix `UniqueFrame::into_raw`\n\n* fix\n\n* fix\n\n* simplify\n\n* simplify\n\n* fmt\n\n* Delete ostd-spec-optimization-review.md\n\n* Update Cargo.lock\n\n* try fix",
          "timestamp": "2026-10-12T05:51:40Z",
          "tree_id": "84f7e9a0eb62f93a18d6ccc3d357d041b629559e",
          "url": "https://github.com/asterinas/vostd/commit/0d139e00d628e23257aa7ec60916df99867698a7"
        },
        "date": 1791784900000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1160242633,
            "extra": "verified=4189 errors=0 smt-run=275,662ms wall=186,677ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 303406520,
            "extra": "smt-run=105,349ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 213237396,
            "extra": "smt-run=35,167ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 89049434,
            "extra": "smt-run=26,081ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,590ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9310756,
            "extra": "smt-run=1,609ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940645,
            "extra": "smt-run=1,319ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=842ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2026397,
            "extra": "smt-run=431ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=563ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "850a3a4ef403fbc8d3492441441ccc7e45b088b3",
          "message": "Introduce architecture paging and address-space models (#710)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-10-14T05:48:47Z",
          "tree_id": "f486b6a335f23e10bc6223daff86503d3e1ca5b5",
          "url": "https://github.com/asterinas/vostd/commit/850a3a4ef403fbc8d3492441441ccc7e45b088b3"
        },
        "date": 1791957663000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1067948682,
            "extra": "verified=4204 errors=0 smt-run=338,584ms wall=230,628ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 293576599,
            "extra": "smt-run=129,873ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 261181945,
            "extra": "smt-run=52,457ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 85603727,
            "extra": "smt-run=32,039ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=4,368ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9310756,
            "extra": "smt-run=2,269ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940645,
            "extra": "smt-run=1,639ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,016ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=872ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=606ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "fa8f72d1a07be87971b97261edf61c20fae79225",
          "message": "fix: level constraint in `Cursor::map` (#828)\n\n* fix: level constraint in `Cursor::map`\n\n* more\n\n* minor",
          "timestamp": "2026-10-14T06:42:42Z",
          "tree_id": "5472deb178e6fcbff10f84ed5d6f49e9f27df0d8",
          "url": "https://github.com/asterinas/vostd/commit/fa8f72d1a07be87971b97261edf61c20fae79225"
        },
        "date": 1791960412000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1101695885,
            "extra": "verified=4205 errors=0 smt-run=273,068ms wall=183,055ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345504281,
            "extra": "smt-run=118,626ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 261181945,
            "extra": "smt-run=39,873ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 58705238,
            "extra": "smt-run=20,933ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,069ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16596367,
            "extra": "smt-run=1,079ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9310756,
            "extra": "smt-run=1,324ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=652ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=525ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1511136,
            "extra": "smt-run=406ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "395015e012954a2fc579d1bff917abc7d4b4e67d",
          "message": "fix: Verus breaking change (#829)\n\n* fix `min` and `max` specifications\n\n* fix",
          "timestamp": "2026-10-15T06:40:03Z",
          "tree_id": "5a09b8ffc8c9b06c896be39cb62d39ce0c5f20c7",
          "url": "https://github.com/asterinas/vostd/commit/395015e012954a2fc579d1bff917abc7d4b4e67d"
        },
        "date": 1792047131000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1101598471,
            "extra": "verified=4205 errors=0 smt-run=323,404ms wall=221,038ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 345504281,
            "extra": "smt-run=132,032ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 261181945,
            "extra": "smt-run=46,982ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 60113039,
            "extra": "smt-run=23,163ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,627ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9310756,
            "extra": "smt-run=2,143ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940645,
            "extra": "smt-run=1,586ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=970ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2026397,
            "extra": "smt-run=552ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=758ms"
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
          "id": "d7d2ebec6b2d131e5d78ca40a052f67ce5b3a87a",
          "message": "docs: update publication links and contribution guidelines in README (#831)",
          "timestamp": "2026-10-16T02:21:50Z",
          "tree_id": "2a3513dde1ec02beebfc2061376ffd9ae6de923c",
          "url": "https://github.com/asterinas/vostd/commit/d7d2ebec6b2d131e5d78ca40a052f67ce5b3a87a"
        },
        "date": 1792118083000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 870237961,
            "extra": "verified=4205 errors=0 smt-run=317,954ms wall=222,494ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 280542868,
            "extra": "smt-run=132,320ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 110011540,
            "extra": "smt-run=26,361ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 54693127,
            "extra": "smt-run=25,816ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=5,098ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9310756,
            "extra": "smt-run=2,570ms"
          },
          {
            "name": "rlimit: utf8",
            "unit": "rlimit",
            "value": 4940645,
            "extra": "smt-run=1,705ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,081ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=888ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=677ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f660cc70d1f2de148cd452f5679a01c66a479cc3",
          "message": "fix: a series of bugs caused by wrong assumptions at the trusted boundary (#830)\n\n* minor\n\n* fix bugs\n\n* remove comments\n\n* simplify\n\n* fix `empty_with_owner` postconditions\n\n* fix `PageTableNode::alloc` postcondition\n\n* minor\n\n* change lemma names\n\n* change lemma names\n\n* remove some proofs\n\n* minor\n\n* remove legacy `slot_perm_reparked_spec`\n\n* minor\n\n* minor\n\n* simplify\n\n* simplify\n\n* simplify\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* simplify `alloc_if_none` postcondition\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* change lemma names\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* change lemma names\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* change lemma names\n\n* minor\n\n* change lemma names\n\n* change lemma names\n\n* change lemma names\n\n* change lemma names\n\n* minor\n\n* change lemma names\n\n* remove `frame_sub_pages_valid`\n\n* remove redundant proofs\n\n* change lemma names\n\n* minor\n\n* change lemma names\n\n* minor\n\n* change lemma names\n\n* change lemma names\n\n* change lemma names\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* change lemma names\n\n* minor\n\n* done\n\n* fmt",
          "timestamp": "2026-10-16T10:31:34Z",
          "tree_id": "0f9d0493fd4a6affda7ab0b557a9ed5f20b27bb0",
          "url": "https://github.com/asterinas/vostd/commit/f660cc70d1f2de148cd452f5679a01c66a479cc3"
        },
        "date": 1792147125000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1116332027,
            "extra": "verified=4208 errors=0 smt-run=425,779ms wall=265,827ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 464998252,
            "extra": "smt-run=212,589ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 110011540,
            "extra": "smt-run=28,329ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 86531186,
            "extra": "smt-run=29,523ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=5,420ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16596367,
            "extra": "smt-run=1,876ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 9310756,
            "extra": "smt-run=2,589ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,098ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927493,
            "extra": "smt-run=1,002ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=663ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c6e2fe4f691f5421aee9de1fab4dc85b40b0b002",
          "message": "chore: use `FrameRawPerms` in `PageTableConfig` (#834)\n\n* use `FrameRawPerms` in `PageTableConfig`\n\n* update irc11 verus version",
          "timestamp": "2026-10-17T13:30:59Z",
          "tree_id": "22330bbafe132b4f2d2aedbe5f1dbde5e72d4a56",
          "url": "https://github.com/asterinas/vostd/commit/c6e2fe4f691f5421aee9de1fab4dc85b40b0b002"
        },
        "date": 1792244635000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1326022533,
            "extra": "verified=4208 errors=0 smt-run=322,754ms wall=203,803ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 516347013,
            "extra": "smt-run=159,667ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 122013001,
            "extra": "smt-run=23,656ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 83145158,
            "extra": "smt-run=24,366ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,400ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,250ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=1,835ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=767ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=644ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=448ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "75352d12980530346c904b09952f2e1117d450c5",
          "message": "fix：remove unsound MMIO addr axiom for huge page (#832)\n\n* fix\n\n* minor\n\n* Minor\n\n* minor\n\n* minor\n\n* minor\n\n* fmt",
          "timestamp": "2026-10-18T05:46:13Z",
          "tree_id": "f32323a9f7748681758370dc9c9aa27217ea8f30",
          "url": "https://github.com/asterinas/vostd/commit/75352d12980530346c904b09952f2e1117d450c5"
        },
        "date": 1792303524000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1195318715,
            "extra": "verified=4210 errors=0 smt-run=337,854ms wall=224,149ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 387624294,
            "extra": "smt-run=157,964ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 122013001,
            "extra": "smt-run=27,156ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 79627889,
            "extra": "smt-run=27,974ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,253ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,211ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=1,873ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=768ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=603ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=425ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "02bc60890d9eacb456f237337374b662541db970",
          "message": "fix: remove unsound MMIO axiom (#835)\n\n* remove mmio axiom\n\n* fmt\n\n* minor\n\n* minor\n\n* minor",
          "timestamp": "2026-10-18T07:37:30Z",
          "tree_id": "9ed3cca2f453e9c01ebde2d9ad15008a169505d9",
          "url": "https://github.com/asterinas/vostd/commit/02bc60890d9eacb456f237337374b662541db970"
        },
        "date": 1792309409000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1640013451,
            "extra": "verified=4210 errors=0 smt-run=391,330ms wall=249,299ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 477266279,
            "extra": "smt-run=63,395ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 457798635,
            "extra": "smt-run=162,116ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 81126722,
            "extra": "smt-run=25,819ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,741ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,574ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=2,232ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=979ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2026397,
            "extra": "smt-run=549ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=787ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b27201e0fa428fa4f3f34db4a076460d86a94ce5",
          "message": "fix more bugs (#836)\n\n* some fixes\n\n* more\n\n* minor\n\n* update spec\n\n* change lemma names\n\n* minor\n\n* minor\n\n* change lemma names\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* fmt\n\n* minor",
          "timestamp": "2026-10-18T11:59:13Z",
          "tree_id": "f15132b9ed41ea5aeb26be44196f2d1fc020da22",
          "url": "https://github.com/asterinas/vostd/commit/b27201e0fa428fa4f3f34db4a076460d86a94ce5"
        },
        "date": 1792325208000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1645346747,
            "extra": "verified=4210 errors=0 smt-run=455,921ms wall=269,041ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 477266279,
            "extra": "smt-run=72,965ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 451143702,
            "extra": "smt-run=209,427ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 81126722,
            "extra": "smt-run=25,029ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,657ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,632ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=2,190ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,007ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=775ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=558ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "etyyuiope@qq.com",
            "name": "Hiroki Chen",
            "username": "hiroki-chen"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1ff524f7f22e1f893e33ce71a9173ccb572607d6",
          "message": "Rcu typed root history (#805)\n\n* Move generic RCU object resources to vstd_extra\n\nKeep the allocation registry, typed block identity, base retire permission, and client-owned object wrapper together in the reusable proof library. OSTD now retains only its root publication history and imports the generic resources.\n\nVerified with default and IRC11 toolchains: vstd_extra (734/757) and ostd (1478/1491), all with zero errors.\n\n* Retain typed identities in IRC11 root histories\n\nExtract the initial typed root state from the weak-memory prototype. Keep the latest registration and client resource linear while retaining persistent block information for every registered allocation.\n\nRelate each non-null native history message to its exact typed pointer, including provenance. Provide a lookup that duplicates only the identity metadata, so stale-message resolution supplies no memory-access or reclamation permission.\n\nValidation: default full verification (1523 OSTD proofs), full IRC11 OSTD verification (1538 proofs), targeted rustfmt/verusfmt, and git diff --check.\n\n* Add fresh typed RCU root publication transition\n\nAppend a fresh registration or null message to RcuRootOwnedGhost while preserving every historical typed identity. Return the previous current object as a linear resource and retain a fresh persistent identity for a new non-null publication.\n\nThis transition moves bookkeeping and client resources only; it does not establish detachment or permission to reclaim the previous allocation.\n\nValidation: default full verification (1523 OSTD proofs), full IRC11 OSTD verification (1539 proofs), targeted rustfmt/verusfmt, and git diff --check.\n\n* Move RCU root histories to vstd_extra\n\nMove the generic root and owned_root modules beside the RCU allocation resources, preserving the irc11 feature gate. Only module declarations, imports, and documentation change; specifications and proof bodies are unchanged.\n\nValidation: make; cargo dv verify --targets vstd_extra --features irc11,vstd/weak-memory; cargo dv verify --targets ostd --features irc11,vstd/weak-memory; verusfmt 0.7.4 --check on changed Rust files.",
          "timestamp": "2026-10-18T19:16:33Z",
          "tree_id": "a17016e339f93c72bf887988ffa1bd06975d00d9",
          "url": "https://github.com/asterinas/vostd/commit/1ff524f7f22e1f893e33ce71a9173ccb572607d6"
        },
        "date": 1792351451000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1645346747,
            "extra": "verified=4210 errors=0 smt-run=502,672ms wall=285,221ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 477266279,
            "extra": "smt-run=64,782ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 451143702,
            "extra": "smt-run=239,139ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 60093260,
            "extra": "smt-run=27,361ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=5,277ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,826ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=2,823ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,064ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=894ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=679ms"
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
          "id": "f77d98eac27a76e5864af9bc19b861be7eb0fa6d",
          "message": "fmt: update verus dependencies to 2026-10-18 (#839)",
          "timestamp": "2026-10-19T10:44:39Z",
          "tree_id": "6d44141ae81e887cd2031ab9e76de7e15ab71c51",
          "url": "https://github.com/asterinas/vostd/commit/f77d98eac27a76e5864af9bc19b861be7eb0fa6d"
        },
        "date": 1792407648000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1645346745,
            "extra": "verified=4209 errors=0 smt-run=335,061ms wall=201,016ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 477266279,
            "extra": "smt-run=54,998ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 451143702,
            "extra": "smt-run=152,794ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 81126722,
            "extra": "smt-run=19,646ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,147ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=984ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=1,464ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=593ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2026397,
            "extra": "smt-run=381ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=532ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "eafc1c6fd9878e1daf7699d014349732a517218a",
          "message": "fix: addr range in `Cursor` and `PageTable` models (#837)\n\n* fix `try_traverse_and_lock_subtree_root` source code\n\n* fix: clarify `Cursor` range\n\n* minor\n\n* rename\n\n* remove `LOCKED_END_BOUND_spec`\n\n* make `leading_bits_spec` a derived function\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* fmt\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* change lemma names\n\n* change lemma names\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* minor\n\n* change function names\n\n* remove a redundant spec fn\n\n* rename\n\n* Make the address definitions very clear\n\n* simplification\n\n* minor\n\n* simplify\n\n* simplify\n\n* minor\n\n* minor\n\n* minor\n\n* MINOR\n\n* simplify\n\n* minor\n\n* simpify\n\n* fmt\n\n* strip and fmt\n\n* minor\n\n* strip\n\n* migrate latest overflow check\n\n* minor",
          "timestamp": "2026-10-20T06:03:22Z",
          "tree_id": "e621e33ea1a34dd085fa8aee165437d138216243",
          "url": "https://github.com/asterinas/vostd/commit/eafc1c6fd9878e1daf7699d014349732a517218a"
        },
        "date": 1792477492000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1571441111,
            "extra": "verified=4213 errors=0 smt-run=479,689ms wall=285,400ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 580605672,
            "extra": "smt-run=237,413ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 278272574,
            "extra": "smt-run=50,186ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 66408459,
            "extra": "smt-run=28,078ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=5,030ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,724ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=2,962ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,148ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2026397,
            "extra": "smt-run=793ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=979ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "5607f83349069f5b9d026cbca0ffa9ce7e81996b",
          "message": "chore: simplify `crate::specs` import (#840)\n\n* chore: simplify `crate::specs` import\n\n* minor",
          "timestamp": "2026-10-20T06:56:17Z",
          "tree_id": "2b67cd9af24fe950af405e6e8efa5b04815d69ce",
          "url": "https://github.com/asterinas/vostd/commit/5607f83349069f5b9d026cbca0ffa9ce7e81996b"
        },
        "date": 1792480326000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1571441111,
            "extra": "verified=4213 errors=0 smt-run=471,573ms wall=270,975ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 580605672,
            "extra": "smt-run=228,181ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 278272574,
            "extra": "smt-run=52,817ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 66408459,
            "extra": "smt-run=28,369ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=5,167ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,776ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=2,702ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,074ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=945ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=694ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1d827c0f3dd9cf6f055b46d4055547d7190de008",
          "message": "fix: constant requirements in `PageTableConfig` (#841)\n\n* remove a false requirement\n\n* fix: `PageTableConfig` constant requirements\n\n* simplify",
          "timestamp": "2026-10-20T07:45:15Z",
          "tree_id": "b380bf769ebcf2975e142e7be2dd27fb7ddc75e4",
          "url": "https://github.com/asterinas/vostd/commit/1d827c0f3dd9cf6f055b46d4055547d7190de008"
        },
        "date": 1792482780000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1577882115,
            "extra": "verified=4213 errors=0 smt-run=358,448ms wall=211,299ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 559437344,
            "extra": "smt-run=176,244ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 278272574,
            "extra": "smt-run=34,633ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 89465546,
            "extra": "smt-run=28,637ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=2,895ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,078ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=1,368ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=668ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=563ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=427ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1f28475dea772d3c3203d1f580296cfd046fd30c",
          "message": "chore: remove redundant `let ghost` (#842)\n\n* minor\n\n* move `is_aligned` spec to `vstd_extra`\n\n* minor\n\n* minor\n\n* remove unused ghost definitions\n\n* fmt",
          "timestamp": "2026-10-20T08:29:52Z",
          "tree_id": "bf59edf6469faabc746b26b272b70662252df329",
          "url": "https://github.com/asterinas/vostd/commit/1f28475dea772d3c3203d1f580296cfd046fd30c"
        },
        "date": 1792485581000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1502503310,
            "extra": "verified=4213 errors=0 smt-run=454,322ms wall=269,244ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 487054534,
            "extra": "smt-run=220,223ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 277053177,
            "extra": "smt-run=40,736ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 89465546,
            "extra": "smt-run=29,575ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=5,210ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,866ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=2,913ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,108ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=893ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=663ms"
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
          "id": "ec3a20a6e8f844d0feddaf5da1db595e86bd4873",
          "message": "sync: dv for multi-architecture target selection (#843)",
          "timestamp": "2026-10-20T11:44:37Z",
          "tree_id": "c77de6f3462da55e29b187da44fdcf0ffed5c6a9",
          "url": "https://github.com/asterinas/vostd/commit/ec3a20a6e8f844d0feddaf5da1db595e86bd4873"
        },
        "date": 1792497027000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1502503310,
            "extra": "verified=4213 errors=0 smt-run=300,358ms wall=193,083ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 487054534,
            "extra": "smt-run=141,663ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 277053177,
            "extra": "smt-run=28,522ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 89465546,
            "extra": "smt-run=21,382ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=2,891ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,111ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=1,656ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=756ms"
          },
          {
            "name": "rlimit: bits",
            "unit": "rlimit",
            "value": 2026397,
            "extra": "smt-run=477ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=551ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "094682336c3f0390e8a840949cee4f02e7b3f78b",
          "message": "Update ci-irc11.yml (#845)",
          "timestamp": "2026-10-21T06:53:25Z",
          "tree_id": "58879d097d95448419249774da5a62f96fb7770c",
          "url": "https://github.com/asterinas/vostd/commit/094682336c3f0390e8a840949cee4f02e7b3f78b"
        },
        "date": 1792566494000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1510826520,
            "extra": "verified=4225 errors=0 smt-run=534,557ms wall=304,424ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 487098694,
            "extra": "smt-run=251,529ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 277053177,
            "extra": "smt-run=56,176ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "unit": "rlimit",
            "value": 89465546,
            "extra": "smt-run=40,271ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=5,202ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,941ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=3,037ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=1,196ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=1,075ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=723ms"
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
          "id": "048c0c307e5f29ea1f882b146b89b6eb3927cc7d",
          "message": "skills: gate documentation findings in vostd-code-review (#846)",
          "timestamp": "2026-10-22T03:46:44Z",
          "tree_id": "469d2707e343e523cfdeb51870e2a859a0803322",
          "url": "https://github.com/asterinas/vostd/commit/048c0c307e5f29ea1f882b146b89b6eb3927cc7d"
        },
        "date": 1792641645000,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "unit": "rlimit",
            "value": 1510814015,
            "extra": "verified=4256 errors=0 smt-run=364,317ms wall=218,492ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "unit": "rlimit",
            "value": 487098694,
            "extra": "smt-run=173,259ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "unit": "rlimit",
            "value": 277053177,
            "extra": "smt-run=41,002ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "unit": "rlimit",
            "value": 75853096,
            "extra": "smt-run=21,872ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "unit": "rlimit",
            "value": 19423556,
            "extra": "smt-run=3,432ms"
          },
          {
            "name": "rlimit: endian",
            "unit": "rlimit",
            "value": 16369438,
            "extra": "smt-run=1,225ms"
          },
          {
            "name": "rlimit: seq_lib",
            "unit": "rlimit",
            "value": 11196458,
            "extra": "smt-run=1,882ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "unit": "rlimit",
            "value": 3602253,
            "extra": "smt-run=790ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "unit": "rlimit",
            "value": 1927495,
            "extra": "smt-run=632ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "unit": "rlimit",
            "value": 1512725,
            "extra": "smt-run=486ms"
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
          "id": "ed4f63f4bcc4718ba4d56f04992f07dd59628ae3",
          "message": "ci: restore perf benchmark publishing and baseline caching (#848)",
          "timestamp": "2026-10-22T16:09:57+08:00",
          "tree_id": "7cb01e6e9fdc4dd6ca452555160e8d87408aaad7",
          "url": "https://github.com/asterinas/vostd/commit/ed4f63f4bcc4718ba4d56f04992f07dd59628ae3"
        },
        "date": 1792656998777,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1510953234,
            "unit": "rlimit",
            "extra": "verified=4259 errors=0 smt-run=340,606ms wall=217,186ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 487098694,
            "unit": "rlimit",
            "extra": "smt-run=157,053ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 277053177,
            "unit": "rlimit",
            "extra": "smt-run=32,184ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 89465546,
            "unit": "rlimit",
            "extra": "smt-run=23,121ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=3,317ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,319ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,010ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=893ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2026397,
            "unit": "rlimit",
            "extra": "smt-run=599ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=669ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0070efdf1f03e7b8c700147de6f205612ffe94c1",
          "message": "ci: use `ubuntu-latest` and add perf comment mechanism (#850)\n\n* update `id-alloc` version status\n\n* update CI\n\n* sync dv\n\n* update perf comment mechanism\n\n* minor",
          "timestamp": "2026-10-22T17:26:12+08:00",
          "tree_id": "430dd0738e7f987cc47bff832cbff4815045882b",
          "url": "https://github.com/asterinas/vostd/commit/0070efdf1f03e7b8c700147de6f205612ffe94c1"
        },
        "date": 1792661649493,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1510953234,
            "unit": "rlimit",
            "extra": "verified=4259 errors=0 smt-run=437,449ms wall=262,621ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 487098694,
            "unit": "rlimit",
            "extra": "smt-run=209,369ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 277053177,
            "unit": "rlimit",
            "extra": "smt-run=42,962ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 89465546,
            "unit": "rlimit",
            "extra": "smt-run=31,735ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,348ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,614ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,453ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=985ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=844ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=585ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "971df8434896031462149bdecb81c0ee5d0424cd",
          "message": "ci: fix perf-comment (#852)",
          "timestamp": "2026-10-22T18:02:52+08:00",
          "tree_id": "b59ccef3948f2007c56fc3d1215cfdc5607b5299",
          "url": "https://github.com/asterinas/vostd/commit/971df8434896031462149bdecb81c0ee5d0424cd"
        },
        "date": 1792663814384,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1510953234,
            "unit": "rlimit",
            "extra": "verified=4259 errors=0 smt-run=507,053ms wall=285,667ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 487098694,
            "unit": "rlimit",
            "extra": "smt-run=240,775ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 277053177,
            "unit": "rlimit",
            "extra": "smt-run=55,814ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 89465546,
            "unit": "rlimit",
            "extra": "smt-run=34,671ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,794ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,784ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,736ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,089ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=925ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=667ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "90378f6ef32773bce86a537c3a7243932d08a689",
          "message": "chore: simplify `node\\entry.rs` (#851)\n\n* simplify\n\n* minor\n\n* minor",
          "timestamp": "2026-10-22T22:49:03+08:00",
          "tree_id": "b727caf5f0f1075279cb5c903a1826ddd999d63e",
          "url": "https://github.com/asterinas/vostd/commit/90378f6ef32773bce86a537c3a7243932d08a689"
        },
        "date": 1792680904092,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1513185472,
            "unit": "rlimit",
            "extra": "verified=4258 errors=0 smt-run=338,315ms wall=219,568ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 487098694,
            "unit": "rlimit",
            "extra": "smt-run=160,072ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 277053177,
            "unit": "rlimit",
            "extra": "smt-run=34,414ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 89465546,
            "unit": "rlimit",
            "extra": "smt-run=23,006ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=3,579ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,236ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=1,803ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=808ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2026397,
            "unit": "rlimit",
            "extra": "smt-run=572ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=635ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "18aea7a127610ad471325235b85395afe82710da",
          "message": "fix: breaking change because of a missing constant (#853)\n\n* fix a breaking change\n\n* Update ci-irc11.yml\n\n* try to fix",
          "timestamp": "2026-10-23T16:06:13+08:00",
          "tree_id": "a7d6a42f0b9cd188f04bbcaaaa40e4d0af3e0123",
          "url": "https://github.com/asterinas/vostd/commit/18aea7a127610ad471325235b85395afe82710da"
        },
        "date": 1792743542606,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1409358849,
            "unit": "rlimit",
            "extra": "verified=4259 errors=0 smt-run=431,750ms wall=259,873ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 487396573,
            "unit": "rlimit",
            "extra": "smt-run=214,190ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 207567185,
            "unit": "rlimit",
            "extra": "smt-run=37,490ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 75341681,
            "unit": "rlimit",
            "extra": "smt-run=28,786ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,641ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,591ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,260ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=992ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2026397,
            "unit": "rlimit",
            "extra": "smt-run=567ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=832ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0e46d8246b29659c4fbdd3027b50af78d0f4b424",
          "message": "fix: minor breaking change (#861)\n\n* fix: remove external spec\n\n* Update ci-irc11.yml",
          "timestamp": "2026-10-25T22:32:04+08:00",
          "tree_id": "ff89a3b68ea364a9eadf1ba4e70465bddb4ee62d",
          "url": "https://github.com/asterinas/vostd/commit/0e46d8246b29659c4fbdd3027b50af78d0f4b424"
        },
        "date": 1792939456979,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1509152800,
            "unit": "rlimit",
            "extra": "verified=4259 errors=0 smt-run=459,773ms wall=266,415ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 487098826,
            "unit": "rlimit",
            "extra": "smt-run=217,849ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 277053177,
            "unit": "rlimit",
            "extra": "smt-run=42,181ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 89465546,
            "unit": "rlimit",
            "extra": "smt-run=36,091ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,690ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,694ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,687ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,043ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=912ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=630ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "ngan.tran@live.com",
            "name": "Cruz Man",
            "username": "numbermuncher11"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "36e90fe192753dbd05c45e175b8c1a2abf4083b3",
          "message": "Fix empty-set partition specification (#862)",
          "timestamp": "2026-10-26T11:25:26+08:00",
          "tree_id": "4e4ff766c703b3610c9790b5acceaf478e73b738",
          "url": "https://github.com/asterinas/vostd/commit/36e90fe192753dbd05c45e175b8c1a2abf4083b3"
        },
        "date": 1792985956605,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1509156921,
            "unit": "rlimit",
            "extra": "verified=4260 errors=0 smt-run=467,723ms wall=271,821ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 487098826,
            "unit": "rlimit",
            "extra": "smt-run=229,607ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 277053177,
            "unit": "rlimit",
            "extra": "smt-run=42,982ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 89465546,
            "unit": "rlimit",
            "extra": "smt-run=31,045ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=5,036ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,674ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,806ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,088ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=876ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=652ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1ddcc81db2c7bd5278aa5221764c62d3a8ad33db",
          "message": "chore: add `Frame::slot_vaddr` (#864)\n\n* chore: add `Frame::slot_vaddr`\n\n* fmt\n\n* minor",
          "timestamp": "2026-10-26T16:18:45+08:00",
          "tree_id": "8e5e803844cb844622ac019019fe2f14ae5ab617",
          "url": "https://github.com/asterinas/vostd/commit/1ddcc81db2c7bd5278aa5221764c62d3a8ad33db"
        },
        "date": 1793004242993,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1473465198,
            "unit": "rlimit",
            "extra": "verified=4260 errors=0 smt-run=330,502ms wall=198,635ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 538222141,
            "unit": "rlimit",
            "extra": "smt-run=180,250ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 233546323,
            "unit": "rlimit",
            "extra": "smt-run=26,743ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 65216734,
            "unit": "rlimit",
            "extra": "smt-run=18,222ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=3,360ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,091ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=1,622ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=618ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2026397,
            "unit": "rlimit",
            "extra": "smt-run=374ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=539ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "2f621c2bbe5ab8ea913485963d80a425385797dd",
          "message": "add RISC-V arch support (#847)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-10-26T17:49:34+08:00",
          "tree_id": "596e31b9b873d36bd5d17074325ea03b8cf52366",
          "url": "https://github.com/asterinas/vostd/commit/2f621c2bbe5ab8ea913485963d80a425385797dd"
        },
        "date": 1793011076418,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1469886850,
            "unit": "rlimit",
            "extra": "verified=4260 errors=0 smt-run=383,315ms wall=227,363ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 538222141,
            "unit": "rlimit",
            "extra": "smt-run=196,608ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 233546323,
            "unit": "rlimit",
            "extra": "smt-run=35,119ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 74490006,
            "unit": "rlimit",
            "extra": "smt-run=23,206ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=3,837ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,332ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=1,937ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=785ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=641ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=487ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "fa4b7e68e5d6713906eeaa901bec6644f97415d5",
          "message": "fix `LinkedList::push_back` exec code and strngthen `LinkedList::cursor_mut_at` postcondition (#866)\n\n* fix wrong `LinkedList::push_back` executable code\n\n* fix `lemma_push_back_embedded`\n\n* strengthen `LinkedList::cursor_mut_at` postcondition",
          "timestamp": "2026-10-27T11:51:33+08:00",
          "tree_id": "8f51626448a591f99f8d9d30fbee9cc19226b5aa",
          "url": "https://github.com/asterinas/vostd/commit/fa4b7e68e5d6713906eeaa901bec6644f97415d5"
        },
        "date": 1793073473479,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1470040099,
            "unit": "rlimit",
            "extra": "verified=4260 errors=0 smt-run=497,680ms wall=285,843ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 538222141,
            "unit": "rlimit",
            "extra": "smt-run=247,230ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 233732906,
            "unit": "rlimit",
            "extra": "smt-run=49,014ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 65216734,
            "unit": "rlimit",
            "extra": "smt-run=31,685ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=5,263ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,702ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,797ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,071ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=886ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=655ms"
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
          "id": "e8164a7b6f80a2e239a5ca23b950b14aab86079a",
          "message": "ci: add risc-v verify (#867)\n\n* ci: add riscv64imac verify\n\n* fix: riscv error\n\n* chore: update Makefile for riscv\n\n* sync: dv",
          "timestamp": "2026-10-27T13:03:38+08:00",
          "tree_id": "c127b6b778a894ef72f13ef567bb7bff04ad9d80",
          "url": "https://github.com/asterinas/vostd/commit/e8164a7b6f80a2e239a5ca23b950b14aab86079a"
        },
        "date": 1793077931961,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1470046281,
            "unit": "rlimit",
            "extra": "verified=4260 errors=0 smt-run=385,758ms wall=230,994ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 538222141,
            "unit": "rlimit",
            "extra": "smt-run=199,256ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 233732906,
            "unit": "rlimit",
            "extra": "smt-run=36,809ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 65216734,
            "unit": "rlimit",
            "extra": "smt-run=23,813ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=3,899ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,308ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=1,943ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=810ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=640ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=467ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9833e14bb4ede64a400ddf40456a1ecdbd5686f4",
          "message": "fix: `LinkedList` API exec code (#868)\n\n* strengthen `LinkedList::push_front` postcondition\n\n* minor\n\n* fix: `LinkedList` API exec code",
          "timestamp": "2026-10-27T15:02:26+08:00",
          "tree_id": "1e6de07d30d40bba15e3d66540f80d027750d76d",
          "url": "https://github.com/asterinas/vostd/commit/9833e14bb4ede64a400ddf40456a1ecdbd5686f4"
        },
        "date": 1793084932498,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1452147570,
            "unit": "rlimit",
            "extra": "verified=4262 errors=0 smt-run=508,883ms wall=289,873ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 538222141,
            "unit": "rlimit",
            "extra": "smt-run=264,383ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 215835661,
            "unit": "rlimit",
            "extra": "smt-run=44,931ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 65216734,
            "unit": "rlimit",
            "extra": "smt-run=30,313ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=5,108ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,841ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,727ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,134ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=947ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=709ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "4a98896f7ecfd0a4fb7d31612a611670b73295c9",
          "message": "breaking change: `nonzero_internal` is no longer required (#869)\n\n* remove `nonzero_internals` feature\n\n* Update ci-irc11.yml\n\n* fix patch",
          "timestamp": "2026-10-28T11:24:23+08:00",
          "tree_id": "37276412ac35bd9923046bad7e609964ddf2b85c",
          "url": "https://github.com/asterinas/vostd/commit/4a98896f7ecfd0a4fb7d31612a611670b73295c9"
        },
        "date": 1793158795224,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1451537969,
            "unit": "rlimit",
            "extra": "verified=4262 errors=0 smt-run=404,091ms wall=235,753ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 538222141,
            "unit": "rlimit",
            "extra": "smt-run=203,849ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 215835661,
            "unit": "rlimit",
            "extra": "smt-run=41,115ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 74490006,
            "unit": "rlimit",
            "extra": "smt-run=21,478ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=3,611ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,303ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,188ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=802ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=703ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=486ms"
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
          "id": "025280446ae0ffc2df56a280a43cca78b0f3772d",
          "message": "ci: add ci verification dashboard with verification coverage, API links, and performance benchmarks (#871)\n\n* feat: verification dashboard homepage + stats CI pipeline\n\n- tools/verus_stats.py: snapshot + record subcommands using line_count --json,\n  mainline normalize via origin/phaseII/mainline, ostd/src+ostd/libs only\n- tools/site/: ECharts dashboard (tiles, line chart, treemap, tables, tiles)\n  with dark/light CSS scheme\n- ci.yml: add stats job (line_count build + mainline fetch + snapshot),\n  extend perf-history (record history.json on gh-pages),\n  extend doc-deploy (assemble site root: dashboard + verusdoc/ + dev/bench/ + stats/)\n\n* fix(ci): stats job requires bootstrapped tools/verus and mainline fallback\n\n- tools/verus is gitignored: setup-verus with verus: 'false' skips the\n  bootstrap-if-miss step, so the line_count build had no manifest on CI.\n  Use verus: 'true' (as the doc job does) to cache+bootstrap tools/verus.\n- the fork may lack phaseII/mainline: fall back to fetching it from\n  asterinas/vostd when git fetch origin fails.\n- bump job timeout to 60m (cold Verus bootstrap on cache miss)\n\n* feat: four-status treemap, spec-library LoC, merged stats deploy job\n\n- verus_stats.py: scan ostd/specs into spec_all/proof_all for the line\n  chart; port code_treemap.py semantics — unplanned modules (arch\n  boot/iommu/tdx_guest, libs linux-bzimage/ostd-macros/ostd-test), no-twin\n  files count as unverified, align_ext pinned at 24 verified lines;\n  history points carry unplanned too\n- site: treemap re-rendered with a hand-rolled squarify into plain HTML\n  (ECharts nested treemap cannot caption parent rows) — group/platform\n  caption bands, module label chips, four reference status colors, exact\n  tile values in stat tiles, module table sorted by name, no drill-down\n- ci.yml: fold the snapshot into the deploy job renamed `stats` at\n  doc-deploy's position (verify/doc -> perf-history -> stats)\n\n* feat: verified API count from rustdoc JSON in snapshot, tile, and chart\n\n- verus_stats.py: port kverus verus_cov.py's API extraction — count\n  bodyful rustdoc functions that are neither spec/proof-only (internal\n  spec/proof attrs, when_used_as_spec, ../specs files) nor trusted away\n  (external_body), skipping uppercase names, Inline(Hint) trait impls\n  and auto-derived impl items; snapshot --doc-json fills\n  totals.verified_apis and record carries it into history points\n- ci: doc job runs 'cargo dv doc --package ostd --json-output' and\n  uploads doc/ostd.json; the stats deploy job folds it into the snapshot\n- site: 'Unverified' stat tile becomes 'Verified APIs' (281 locally),\n  line chart grows a fifth series (violet slot 5), history table gains\n  an APIs column; verified-API deltas skip points without the field\n- site: swap card order (treemap above the line chart) and trim module\n  label chips to the name (hover tooltips carry the counts)\n\n* feat: per-API list card under the history chart\n\n- verus_stats.py: collect_verified_apis also returns each entry\n  (owner-qualified name, module group, repo-relative location) and the\n  snapshot carries it as verified_apis_list\n- site: 'Verified APIs' card with a View list table (name/module/\n  location) after the line chart; trimmed the treemap/line card notes\n  per review\n\n* Improve Pages coverage visualization and benchmark dashboard\n\n* Correct treemap group labels and trusted boundary terminology\n\n* Widen coverage chart and preserve compact group names\n\n* Fit coverage chart to laptop screens with compact subsystem row\n\n* doc: update readme\n\n* Extract CI steps into composite actions",
          "timestamp": "2026-10-28T16:28:00+08:00",
          "tree_id": "5d2e5f09d049a01821696f8416ad1371ba32ff44",
          "url": "https://github.com/asterinas/vostd/commit/025280446ae0ffc2df56a280a43cca78b0f3772d"
        },
        "date": 1793176540365,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1451537969,
            "unit": "rlimit",
            "extra": "verified=4262 errors=0 smt-run=482,288ms wall=278,835ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 538222141,
            "unit": "rlimit",
            "extra": "smt-run=238,303ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 215835661,
            "unit": "rlimit",
            "extra": "smt-run=47,333ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 74490006,
            "unit": "rlimit",
            "extra": "smt-run=28,022ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,939ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 11196458,
            "unit": "rlimit",
            "extra": "smt-run=2,618ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,054ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2026397,
            "unit": "rlimit",
            "extra": "smt-run=747ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=885ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451903,
            "unit": "rlimit",
            "extra": "smt-run=1,695ms"
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
          "id": "a22d96b40dddb85a4df2896113fb9e7170b86a42",
          "message": "fix: RISC-V mapping proof and add verification to Verus CI workflows (#873)\n\n* fix: RISC-V mapping proof and add verification to Verus CI workflows\n\n* ci: IRC11 verus base update",
          "timestamp": "2026-10-28T19:05:15+08:00",
          "tree_id": "215d1f819156f59a114b8a07c32475faec445d8f",
          "url": "https://github.com/asterinas/vostd/commit/a22d96b40dddb85a4df2896113fb9e7170b86a42"
        },
        "date": 1793186327493,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1344390345,
            "unit": "rlimit",
            "extra": "verified=4262 errors=0 smt-run=426,667ms wall=251,245ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 543754451,
            "unit": "rlimit",
            "extra": "smt-run=218,591ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 92529203,
            "unit": "rlimit",
            "extra": "smt-run=23,186ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 73802104,
            "unit": "rlimit",
            "extra": "smt-run=31,701ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,635ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=1,672ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9170301,
            "unit": "rlimit",
            "extra": "smt-run=2,577ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,030ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=956ms"
          },
          {
            "name": "rlimit: resource::ghost_resource::csum",
            "value": 1512725,
            "unit": "rlimit",
            "extra": "smt-run=684ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "85332676+Je5s1e@users.noreply.github.com",
            "name": "Chao",
            "username": "Je5s1e"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "1d56def9457f321ae5dbf517d9b78f06dc6f15da",
          "message": "fix: correct VmSpace slot specs and verify virtual memory helpers (#859)",
          "timestamp": "2026-10-29T11:15:36+08:00",
          "tree_id": "b7a50ce481cf88970bb5436b2064dd863c432ef3",
          "url": "https://github.com/asterinas/vostd/commit/1d56def9457f321ae5dbf517d9b78f06dc6f15da"
        },
        "date": 1793244157507,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1344824971,
            "unit": "rlimit",
            "extra": "verified=4264 errors=0 smt-run=303,914ms wall=186,335ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 543754451,
            "unit": "rlimit",
            "extra": "smt-run=163,827ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78229690,
            "unit": "rlimit",
            "extra": "smt-run=16,145ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 73802104,
            "unit": "rlimit",
            "extra": "smt-run=21,617ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=2,640ms"
          },
          {
            "name": "rlimit: endian",
            "value": 16369438,
            "unit": "rlimit",
            "extra": "smt-run=968ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9170301,
            "unit": "rlimit",
            "extra": "smt-run=1,390ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=622ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2026397,
            "unit": "rlimit",
            "extra": "smt-run=521ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=469ms"
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
          "id": "9b79efa6fe2dbb905dad61bc9fcbd96e523c39e3",
          "message": "fix: add soundness and bi-injectivity lemmas for rlimit error (#874)\n\n* fix: add soundness and bi-injectivity lemmas for rlimit error\n\n* fix: add soundness and bi-injectivity lemma calls in Segment::drop loop",
          "timestamp": "2026-10-29T13:32:13+08:00",
          "tree_id": "aeb18982f12f4fd82133b5cfac1c5931c769107e",
          "url": "https://github.com/asterinas/vostd/commit/9b79efa6fe2dbb905dad61bc9fcbd96e523c39e3"
        },
        "date": 1793252317913,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1344855759,
            "unit": "rlimit",
            "extra": "verified=4264 errors=0 smt-run=471,970ms wall=279,936ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 543754451,
            "unit": "rlimit",
            "extra": "smt-run=243,680ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78229690,
            "unit": "rlimit",
            "extra": "smt-run=29,946ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 73802104,
            "unit": "rlimit",
            "extra": "smt-run=31,356ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=5,426ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9170301,
            "unit": "rlimit",
            "extra": "smt-run=2,715ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3602253,
            "unit": "rlimit",
            "extra": "smt-run=1,152ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2026397,
            "unit": "rlimit",
            "extra": "smt-run=784ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1927495,
            "unit": "rlimit",
            "extra": "smt-run=960ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451903,
            "unit": "rlimit",
            "extra": "smt-run=1,822ms"
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
          "id": "9b79efa6fe2dbb905dad61bc9fcbd96e523c39e3",
          "message": "fix: add soundness and bi-injectivity lemmas for rlimit error (#874)\n\n* fix: add soundness and bi-injectivity lemmas for rlimit error\n\n* fix: add soundness and bi-injectivity lemma calls in Segment::drop loop",
          "timestamp": "2026-10-29T13:32:13+08:00",
          "tree_id": "aeb18982f12f4fd82133b5cfac1c5931c769107e",
          "url": "https://github.com/asterinas/vostd/commit/9b79efa6fe2dbb905dad61bc9fcbd96e523c39e3"
        },
        "date": 1793260848313,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1747164752,
            "unit": "rlimit",
            "extra": "verified=4264 errors=0 smt-run=343,676ms wall=212,781ms"
          },
          {
            "name": "rlimit: mm::frame::segment",
            "value": 616623310,
            "unit": "rlimit",
            "extra": "smt-run=42,541ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 558156207,
            "unit": "rlimit",
            "extra": "smt-run=163,754ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 59946094,
            "unit": "rlimit",
            "extra": "smt-run=20,598ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=3,149ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845987,
            "unit": "rlimit",
            "extra": "smt-run=1,057ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9172309,
            "unit": "rlimit",
            "extra": "smt-run=1,622ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3180666,
            "unit": "rlimit",
            "extra": "smt-run=728ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=521ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951672,
            "unit": "rlimit",
            "extra": "smt-run=564ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d0c4661f681b0b77b06507cfabb27f2eaebfede7",
          "message": "fix: strengthen `Linkedlist::contains/cursor_mut_at` postconditions and remove `TrackDrop for LinkedList` (#875)\n\n* fix `LinkedList::contains`\n\n* fmt\n\n* remove `TrackDrop for LinkedList`\n\n* minor\n\n* simplify\n\n* rename a field\n\n* minor\n\n* simplify",
          "timestamp": "2026-10-29T16:08:26+08:00",
          "tree_id": "6d64c129c5ee4c6de83060d5cfbf5bcc4b4d4454",
          "url": "https://github.com/asterinas/vostd/commit/d0c4661f681b0b77b06507cfabb27f2eaebfede7"
        },
        "date": 1793261710388,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1762034293,
            "unit": "rlimit",
            "extra": "verified=4261 errors=0 smt-run=517,407ms wall=295,682ms"
          },
          {
            "name": "rlimit: mm::frame::segment",
            "value": 632632317,
            "unit": "rlimit",
            "extra": "smt-run=64,844ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 558156875,
            "unit": "rlimit",
            "extra": "smt-run=247,348ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 81628070,
            "unit": "rlimit",
            "extra": "smt-run=31,404ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,937ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9172309,
            "unit": "rlimit",
            "extra": "smt-run=2,709ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218523,
            "unit": "rlimit",
            "extra": "smt-run=1,852ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3180666,
            "unit": "rlimit",
            "extra": "smt-run=1,050ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=815ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951672,
            "unit": "rlimit",
            "extra": "smt-run=900ms"
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
          "id": "1ffc599bfe497a7c6a5f115b4e3c9e4aa46a6293",
          "message": "performance: mm::frame::segment (#876)",
          "timestamp": "2026-10-29T16:25:00+08:00",
          "tree_id": "cd039c364de2718d0048511a304ae69d04c7f8ee",
          "url": "https://github.com/asterinas/vostd/commit/1ffc599bfe497a7c6a5f115b4e3c9e4aa46a6293"
        },
        "date": 1793262795910,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1179334038,
            "unit": "rlimit",
            "extra": "verified=4262 errors=0 smt-run=490,467ms wall=288,495ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 558156875,
            "unit": "rlimit",
            "extra": "smt-run=269,257ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 81628070,
            "unit": "rlimit",
            "extra": "smt-run=32,328ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 59946094,
            "unit": "rlimit",
            "extra": "smt-run=34,071ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=5,010ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9172309,
            "unit": "rlimit",
            "extra": "smt-run=2,537ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218523,
            "unit": "rlimit",
            "extra": "smt-run=1,699ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3180666,
            "unit": "rlimit",
            "extra": "smt-run=1,098ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=793ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951672,
            "unit": "rlimit",
            "extra": "smt-run=929ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9c7677deee6fbe7ac154158b571282a801ecea8a",
          "message": "chore: minor simplification in `Frame::drop` spec and `UniqueFrame` proof (#877)\n\n* minor simplification\n\n* Update mod.rs",
          "timestamp": "2026-10-29T17:20:55+08:00",
          "tree_id": "7ee9e4980b5fbbf5e4e257802bce8ee81cccb1e5",
          "url": "https://github.com/asterinas/vostd/commit/9c7677deee6fbe7ac154158b571282a801ecea8a"
        },
        "date": 1793266052027,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1112982595,
            "unit": "rlimit",
            "extra": "verified=4261 errors=0 smt-run=426,770ms wall=261,788ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 501805754,
            "unit": "rlimit",
            "extra": "smt-run=221,381ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83138179,
            "unit": "rlimit",
            "extra": "smt-run=29,014ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57926721,
            "unit": "rlimit",
            "extra": "smt-run=27,213ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=4,915ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845987,
            "unit": "rlimit",
            "extra": "smt-run=1,611ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9172309,
            "unit": "rlimit",
            "extra": "smt-run=2,536ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3180666,
            "unit": "rlimit",
            "extra": "smt-run=1,015ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=770ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951672,
            "unit": "rlimit",
            "extra": "smt-run=886ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "c04b45050cbda20954939277c24537470189e868",
          "message": "verify tlb range op and cpu iter (#838)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-10-29T17:38:19+08:00",
          "tree_id": "70484aab3bc5f6b8f75e9d32241f7c0e551b978d",
          "url": "https://github.com/asterinas/vostd/commit/c04b45050cbda20954939277c24537470189e868"
        },
        "date": 1793267557444,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1113065643,
            "unit": "rlimit",
            "extra": "verified=4263 errors=0 smt-run=460,029ms wall=281,276ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 501805754,
            "unit": "rlimit",
            "extra": "smt-run=239,871ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83138179,
            "unit": "rlimit",
            "extra": "smt-run=28,299ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57926721,
            "unit": "rlimit",
            "extra": "smt-run=28,971ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=5,279ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9172309,
            "unit": "rlimit",
            "extra": "smt-run=2,581ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3180666,
            "unit": "rlimit",
            "extra": "smt-run=1,139ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=822ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951672,
            "unit": "rlimit",
            "extra": "smt-run=973ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,695ms"
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
          "id": "5877493508f84824a17ca85f21b42a5438a5b084",
          "message": "perf: reduce verification cost through loop isolation and localized proofs (#878)\n\n* perf: loop_isolation\n\n* perf: move_forward\n\n* perf: reduce verification cost by localizing proof contexts\n\n* fix: IRC11",
          "timestamp": "2026-10-29T18:22:19+08:00",
          "tree_id": "b3f7e22b9f05898b6cca663a91d2d852cfc6e545",
          "url": "https://github.com/asterinas/vostd/commit/5877493508f84824a17ca85f21b42a5438a5b084"
        },
        "date": 1793269730246,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 920922061,
            "unit": "rlimit",
            "extra": "verified=4266 errors=0 smt-run=389,519ms wall=257,758ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 370434897,
            "unit": "rlimit",
            "extra": "smt-run=183,751ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 85292154,
            "unit": "rlimit",
            "extra": "smt-run=32,779ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 71288758,
            "unit": "rlimit",
            "extra": "smt-run=29,167ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 19423556,
            "unit": "rlimit",
            "extra": "smt-run=5,242ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845987,
            "unit": "rlimit",
            "extra": "smt-run=1,769ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9172309,
            "unit": "rlimit",
            "extra": "smt-run=2,720ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3180666,
            "unit": "rlimit",
            "extra": "smt-run=1,124ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=803ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951672,
            "unit": "rlimit",
            "extra": "smt-run=926ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "acd94a702714e593bfe9c4af383337b8f9aaedbb",
          "message": "Add LoongArch architecture support (#865)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-10-30T13:59:17+08:00",
          "tree_id": "5a3499db402ece02fb7a41e15487461ae90c6a07",
          "url": "https://github.com/asterinas/vostd/commit/acd94a702714e593bfe9c4af383337b8f9aaedbb"
        },
        "date": 1793340846176,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 882679620,
            "unit": "rlimit",
            "extra": "verified=4266 errors=0 smt-run=245,857ms wall=177,878ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=113,797ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=19,418ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57981152,
            "unit": "rlimit",
            "extra": "smt-run=16,619ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707233,
            "unit": "rlimit",
            "extra": "smt-run=1,910ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,257ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,215ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=770ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=544ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=604ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "225f6ef1c0f5727e8a6b3594fe26b9c8233f7743",
          "message": "fix: revoke several adapted code (#880)\n\n* use for loop\n\n* more fix\n\n* revoke `range_alloc`",
          "timestamp": "2026-10-30T17:13:40+08:00",
          "tree_id": "fe4f3e75e5aaabb9c6e38e6391a3e033c2b4b066",
          "url": "https://github.com/asterinas/vostd/commit/225f6ef1c0f5727e8a6b3594fe26b9c8233f7743"
        },
        "date": 1793352003599,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906010130,
            "unit": "rlimit",
            "extra": "verified=4266 errors=0 smt-run=416,442ms wall=277,689ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=202,646ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=35,044ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57981152,
            "unit": "rlimit",
            "extra": "smt-run=27,891ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707233,
            "unit": "rlimit",
            "extra": "smt-run=2,799ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,831ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,698ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,245ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=828ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=996ms"
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
          "id": "9f83048b67b62b6b226800b1eef8798164113821",
          "message": "skills: improve with API contract checks and PR checkout support (#881)",
          "timestamp": "2026-10-30T21:17:23+08:00",
          "tree_id": "5c4fb7c603a6f56b2770b5210d97608504288529",
          "url": "https://github.com/asterinas/vostd/commit/9f83048b67b62b6b226800b1eef8798164113821"
        },
        "date": 1793367716143,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906010130,
            "unit": "rlimit",
            "extra": "verified=4266 errors=0 smt-run=336,674ms wall=234,886ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=160,660ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=24,129ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57981152,
            "unit": "rlimit",
            "extra": "smt-run=24,156ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707233,
            "unit": "rlimit",
            "extra": "smt-run=2,595ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,735ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,734ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=983ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=798ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=858ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "85332676+Je5s1e@users.noreply.github.com",
            "name": "Chao",
            "username": "Je5s1e"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "020b85418e2d4edcd5089cbf818e477b1d07f3ea",
          "message": "fix: verify IRQ guard transfer and pointer helpers (#858)\n\n* fix: verify IRQ guard transfer and pointer helpers\n\n* Resolve upstream conflicts and simplify IRQ and pointer verification\n\n* Simplify IRQ and array layout verification comments",
          "timestamp": "2026-10-30T21:55:26+08:00",
          "tree_id": "4d51ab0c8c4df8edf0d7d22acb5177ce11ada63b",
          "url": "https://github.com/asterinas/vostd/commit/020b85418e2d4edcd5089cbf818e477b1d07f3ea"
        },
        "date": 1793368889399,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906014779,
            "unit": "rlimit",
            "extra": "verified=4268 errors=0 smt-run=221,018ms wall=156,635ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=110,701ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=17,783ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57981152,
            "unit": "rlimit",
            "extra": "smt-run=15,488ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845978,
            "unit": "rlimit",
            "extra": "smt-run=823ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707233,
            "unit": "rlimit",
            "extra": "smt-run=1,277ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=829ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=539ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=498ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=444ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "85332676+Je5s1e@users.noreply.github.com",
            "name": "Chao",
            "username": "Je5s1e"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "7c8019b4db19a612bee3feea9ac6825932903ae0",
          "message": "fix: prove DMA coherent frame address bounds (#856)\n\n* fix: prove DMA coherent frame address bounds\n\n* tidy imports and comments in the DMA coherent proof",
          "timestamp": "2026-10-30T23:30:12+08:00",
          "tree_id": "0903ded6d010dbcda1180e848e99d0b209c89e08",
          "url": "https://github.com/asterinas/vostd/commit/7c8019b4db19a612bee3feea9ac6825932903ae0"
        },
        "date": 1793374552157,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906071584,
            "unit": "rlimit",
            "extra": "verified=4268 errors=0 smt-run=276,995ms wall=195,745ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=134,543ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 84319312,
            "unit": "rlimit",
            "extra": "smt-run=18,205ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=21,557ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845978,
            "unit": "rlimit",
            "extra": "smt-run=1,167ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707233,
            "unit": "rlimit",
            "extra": "smt-run=1,852ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,183ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=765ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=593ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=641ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "26d9166f8f3fd943b554bbd34ff48c0536d8eafb",
          "message": "ci: macos-latest (#882)",
          "timestamp": "2026-10-31T12:10:45+08:00",
          "tree_id": "9703553e96328d0327b9269ca200111aaba9d0f6",
          "url": "https://github.com/asterinas/vostd/commit/26d9166f8f3fd943b554bbd34ff48c0536d8eafb"
        },
        "date": 1793420164432,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906071584,
            "unit": "rlimit",
            "extra": "verified=4268 errors=0 smt-run=333,259ms wall=233,714ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=157,179ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=24,216ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57981152,
            "unit": "rlimit",
            "extra": "smt-run=22,823ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707233,
            "unit": "rlimit",
            "extra": "smt-run=2,572ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,683ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,703ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,027ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=790ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=917ms"
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
          "id": "b39a0b35efef9a55e08d93f7639f1c405ed300c3",
          "message": "fmt: cargo lock (#884)",
          "timestamp": "2026-11-02T12:44:40+08:00",
          "tree_id": "05cdc46b34efe181414dba0b2705b4961f255be5",
          "url": "https://github.com/asterinas/vostd/commit/b39a0b35efef9a55e08d93f7639f1c405ed300c3"
        },
        "date": 1793595620529,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906071585,
            "unit": "rlimit",
            "extra": "verified=4268 errors=0 smt-run=336,121ms wall=233,701ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=158,536ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 84319312,
            "unit": "rlimit",
            "extra": "smt-run=24,068ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=26,548ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=2,650ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,704ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,547ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,029ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=790ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=857ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "0c3b9f7a6376ca57e9cd4380974ed2d257f84448",
          "message": "chore: minor adjustment of `NonNull::with_addr` and remove `nonzero_internals` configs (#885)\n\n* Update config.toml\n\n* use `assume_specification` for `NonNull::with_addr``\n\n* minor",
          "timestamp": "2026-11-02T14:13:09+08:00",
          "tree_id": "33fd7f79f773ace489b383ba0abbafd933fe894f",
          "url": "https://github.com/asterinas/vostd/commit/0c3b9f7a6376ca57e9cd4380974ed2d257f84448"
        },
        "date": 1793600752541,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906071585,
            "unit": "rlimit",
            "extra": "verified=4268 errors=0 smt-run=344,995ms wall=238,548ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=165,387ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 84319312,
            "unit": "rlimit",
            "extra": "smt-run=23,039ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=24,539ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=2,578ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,731ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,761ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,008ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=797ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=894ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "323526f8b7ff988ade49e9ab3ddf4f3feb91b794",
          "message": "prove: verify x86 task context (#870)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-02T15:42:27+08:00",
          "tree_id": "3b5732808f19541f6966e9a8ae3ab6c68167fa55",
          "url": "https://github.com/asterinas/vostd/commit/323526f8b7ff988ade49e9ab3ddf4f3feb91b794"
        },
        "date": 1793607068557,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 906086193,
            "unit": "rlimit",
            "extra": "verified=4278 errors=0 smt-run=320,525ms wall=233,933ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=150,598ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=21,770ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57981152,
            "unit": "rlimit",
            "extra": "smt-run=23,257ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=2,277ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,632ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,507ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=953ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=704ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951392,
            "unit": "rlimit",
            "extra": "smt-run=819ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "afb02bd685c8a496edacf50734c6f442601b81cc",
          "message": "Verify memory region constructors and normalization (#797)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-03T11:06:10+08:00",
          "tree_id": "d68776b4eadd48c1b3978a8207bdc22cc669111f",
          "url": "https://github.com/asterinas/vostd/commit/afb02bd685c8a496edacf50734c6f442601b81cc"
        },
        "date": 1793675937866,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 918763863,
            "unit": "rlimit",
            "extra": "verified=4291 errors=0 smt-run=227,333ms wall=163,511ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 362982336,
            "unit": "rlimit",
            "extra": "smt-run=114,301ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 78893838,
            "unit": "rlimit",
            "extra": "smt-run=16,642ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 57981152,
            "unit": "rlimit",
            "extra": "smt-run=15,431ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845978,
            "unit": "rlimit",
            "extra": "smt-run=912ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=1,366ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=908ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=591ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=545ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951386,
            "unit": "rlimit",
            "extra": "smt-run=510ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "803512311e091d65e4b6e3d0839ba30afc729b22",
          "message": "refactor: `FrameRef` permssions (#854)\n\n* fix: `Frame::borrow` lifetime\n\n* progress\n\n* minor fix\n\n* remove `borrow_with_permission`\n\n* minor\n\n* simplify\n\n* minor\n\n* remove `MetaSlotStatus`\n\n* simplify\n\n* minor\n\n* simplify\n\n* minor\n\n* add `FrameRef:start_paddr_spec`\n\n* fmt\n\n* minor\n\n* fix\n\n* add `FrameRef::slot_vaddr`\n\n* fmt\n\n* fix\n\n* change some names\n\n* fmt\n\n* minor\n\n* fix doc\n\n* minor\n\n* fix documentation",
          "timestamp": "2026-11-03T16:07:56+08:00",
          "tree_id": "9fca4e9a7c6e20414cf7f7d83c21d8321365a1a1",
          "url": "https://github.com/asterinas/vostd/commit/803512311e091d65e4b6e3d0839ba30afc729b22"
        },
        "date": 1793695533767,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 952145688,
            "unit": "rlimit",
            "extra": "verified=4289 errors=0 smt-run=236,776ms wall=164,340ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 376782727,
            "unit": "rlimit",
            "extra": "smt-run=122,274ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 82417845,
            "unit": "rlimit",
            "extra": "smt-run=17,282ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 62172257,
            "unit": "rlimit",
            "extra": "smt-run=16,934ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845978,
            "unit": "rlimit",
            "extra": "smt-run=872ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=1,331ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=963ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=567ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=535ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951386,
            "unit": "rlimit",
            "extra": "smt-run=450ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "09a889abadf5a5a965fb848b2d835459bed4c00c",
          "message": "Restore prelude module and commented imports (#888)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-03T16:59:14+08:00",
          "tree_id": "8e7937537dd9279afd890e01c3cf941f8c8d88c9",
          "url": "https://github.com/asterinas/vostd/commit/09a889abadf5a5a965fb848b2d835459bed4c00c"
        },
        "date": 1793696882933,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 952145688,
            "unit": "rlimit",
            "extra": "verified=4289 errors=0 smt-run=380,103ms wall=249,782ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 376782727,
            "unit": "rlimit",
            "extra": "smt-run=185,122ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 82417845,
            "unit": "rlimit",
            "extra": "smt-run=30,416ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 62172257,
            "unit": "rlimit",
            "extra": "smt-run=27,694ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=2,727ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,792ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,822ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,024ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=800ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951386,
            "unit": "rlimit",
            "extra": "smt-run=880ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "291a24c8dd122cc8d6f58f5662e01a471b79c5e8",
          "message": "fix: `FrameRef` field visibility (#889)",
          "timestamp": "2026-11-03T17:19:02+08:00",
          "tree_id": "79d32e15d0e52cd6bb5043b4b9edf63b2e790f0e",
          "url": "https://github.com/asterinas/vostd/commit/291a24c8dd122cc8d6f58f5662e01a471b79c5e8"
        },
        "date": 1793698213353,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1084175217,
            "unit": "rlimit",
            "extra": "verified=4289 errors=0 smt-run=431,081ms wall=268,559ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 466341996,
            "unit": "rlimit",
            "extra": "smt-run=214,284ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 91170810,
            "unit": "rlimit",
            "extra": "smt-run=36,916ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 89301135,
            "unit": "rlimit",
            "extra": "smt-run=33,489ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=2,722ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=2,018ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,053ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=758ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951386,
            "unit": "rlimit",
            "extra": "smt-run=922ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,756ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "f36812787af1c3ef658210259c674f91e73c94c6",
          "message": "prove: verify RISC-V and LoongArch task contexts (#891)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-03T20:44:31+08:00",
          "tree_id": "c0adbc8a3ab07d3e4f3160fe1e4a53f89046e42f",
          "url": "https://github.com/asterinas/vostd/commit/f36812787af1c3ef658210259c674f91e73c94c6"
        },
        "date": 1793710383955,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1082302323,
            "unit": "rlimit",
            "extra": "verified=4290 errors=0 smt-run=480,986ms wall=295,112ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 466341996,
            "unit": "rlimit",
            "extra": "smt-run=244,517ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 91170810,
            "unit": "rlimit",
            "extra": "smt-run=37,302ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 89301135,
            "unit": "rlimit",
            "extra": "smt-run=37,745ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=2,836ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,826ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,819ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,049ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=826ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951386,
            "unit": "rlimit",
            "extra": "smt-run=955ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "6686001fc39720b71d8b79c96246150924ed4d5a",
          "message": "fix: use `NonNull` specification from vstd (#893)\n\n* fix: use `NonNull` specification from vstd\n\n* Update ci-irc11.yml\n\n* Update verus-irc11.patch",
          "timestamp": "2026-11-04T14:39:08+08:00",
          "tree_id": "58187dbf947c925a64634d90cdf80798b821911f",
          "url": "https://github.com/asterinas/vostd/commit/6686001fc39720b71d8b79c96246150924ed4d5a"
        },
        "date": 1793775186240,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1083106826,
            "unit": "rlimit",
            "extra": "verified=4290 errors=0 smt-run=254,367ms wall=164,969ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 466341996,
            "unit": "rlimit",
            "extra": "smt-run=136,123ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 91170810,
            "unit": "rlimit",
            "extra": "smt-run=20,764ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 89301135,
            "unit": "rlimit",
            "extra": "smt-run=18,295ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845978,
            "unit": "rlimit",
            "extra": "smt-run=837ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=1,378ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=895ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=521ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=483ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951386,
            "unit": "rlimit",
            "extra": "smt-run=442ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "4a8b5b49fbd932376c58d9042322f92d5a132edc",
          "message": "ci: update Verus build process (#894)\n\n* Update bootstrap-verus-irc11.sh\n\n* Update bootstrap-verus-irc11.sh\n\n* Update dv",
          "timestamp": "2026-11-04T16:43:09+08:00",
          "tree_id": "a7307081b10e007e8b3926fd72437f9a292248b7",
          "url": "https://github.com/asterinas/vostd/commit/4a8b5b49fbd932376c58d9042322f92d5a132edc"
        },
        "date": 1793782851338,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1083106826,
            "unit": "rlimit",
            "extra": "verified=4290 errors=0 smt-run=424,182ms wall=268,093ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 466341996,
            "unit": "rlimit",
            "extra": "smt-run=219,412ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 91170810,
            "unit": "rlimit",
            "extra": "smt-run=35,457ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 89301135,
            "unit": "rlimit",
            "extra": "smt-run=27,490ms"
          },
          {
            "name": "rlimit: endian",
            "value": 11845978,
            "unit": "rlimit",
            "extra": "smt-run=1,692ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 9707228,
            "unit": "rlimit",
            "extra": "smt-run=2,648ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,962ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3175071,
            "unit": "rlimit",
            "extra": "smt-run=1,049ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=751ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1951386,
            "unit": "rlimit",
            "extra": "smt-run=925ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "4ec330ec227b59f22c4f079db4a757379c3222b7",
          "message": "fix: remove legacy `DerefSpec` and fix a breaking change (#896)\n\n* remove: derefspec\n\n* fmt\n\n* Update ci-irc11.yml",
          "timestamp": "2026-11-05T14:45:14+08:00",
          "tree_id": "a5b3841bdbc2092d9dd8359f649262087036e599",
          "url": "https://github.com/asterinas/vostd/commit/4ec330ec227b59f22c4f079db4a757379c3222b7"
        },
        "date": 1793863030061,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1030519161,
            "unit": "rlimit",
            "extra": "verified=4306 errors=0 smt-run=359,649ms wall=240,985ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 413180286,
            "unit": "rlimit",
            "extra": "smt-run=173,963ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 129306472,
            "unit": "rlimit",
            "extra": "smt-run=28,060ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 80945627,
            "unit": "rlimit",
            "extra": "smt-run=26,390ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,142ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,499ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,381ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=929ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=759ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=690ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "8e4b202d69d1eb706a5fec2f8c3f26f03f841893",
          "message": "Use raw pointer in `Frame` (#892)\n\n* Use raw pointer in `Frame`\n\n* more\n\n* fmt\n\n* minor\n\n* refine\n\n* fmt\n\n* fix `NonNullPtr` for Frame\n\n* fmt\n\n* Update frame_ref.rs\n\n* fix: error in split_while_huge_lemmas in risc-v/loongarch\n\n---------\n\nCo-authored-by: Marsman1996 <lqliuyuwei@outlook.com>",
          "timestamp": "2026-11-07T20:29:05+08:00",
          "tree_id": "7c284965c5abc178c65cd28268a409956dff8a8a",
          "url": "https://github.com/asterinas/vostd/commit/8e4b202d69d1eb706a5fec2f8c3f26f03f841893"
        },
        "date": 1794055717991,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1016760822,
            "unit": "rlimit",
            "extra": "verified=4311 errors=0 smt-run=268,571ms wall=177,327ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 409862457,
            "unit": "rlimit",
            "extra": "smt-run=130,527ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 97497722,
            "unit": "rlimit",
            "extra": "smt-run=34,417ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 77978304,
            "unit": "rlimit",
            "extra": "smt-run=17,741ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=1,316ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=996ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=860ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=604ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=468ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=511ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "aa41304e2a1cb32f556d9c23091441b79747c053",
          "message": "prove: verify x86 execption table (#886)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-09T14:55:21+08:00",
          "tree_id": "24afa77109b33c3dfaf9b98eae9de000312350cd",
          "url": "https://github.com/asterinas/vostd/commit/aa41304e2a1cb32f556d9c23091441b79747c053"
        },
        "date": 1794207712334,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1016907050,
            "unit": "rlimit",
            "extra": "verified=4312 errors=0 smt-run=262,404ms wall=170,639ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 409862457,
            "unit": "rlimit",
            "extra": "smt-run=135,281ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 97497722,
            "unit": "rlimit",
            "extra": "smt-run=27,092ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 77978304,
            "unit": "rlimit",
            "extra": "smt-run=17,771ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=1,272ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=960ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=782ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=622ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=465ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=525ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "58af4bf6efaa5995c84cf1064410d773b3f58031",
          "message": "fix: VmReader/VmWriter postconditions (#899)\n\n* Update io.rs\n\n* fmt",
          "timestamp": "2026-11-10T08:50:06+08:00",
          "tree_id": "9ec86649a7954cb4125e1e07fd9e0db001861c56",
          "url": "https://github.com/asterinas/vostd/commit/58af4bf6efaa5995c84cf1064410d773b3f58031"
        },
        "date": 1794273258810,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1017216747,
            "unit": "rlimit",
            "extra": "verified=4312 errors=0 smt-run=394,518ms wall=249,978ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 409862457,
            "unit": "rlimit",
            "extra": "smt-run=190,453ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 97497722,
            "unit": "rlimit",
            "extra": "smt-run=44,688ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 77978304,
            "unit": "rlimit",
            "extra": "smt-run=29,627ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,539ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,901ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,641ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=984ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=922ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=777ms"
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
          "id": "7d4224a4e0cf102ab78f8df041c013aad40c98bf",
          "message": "prove: arch/x86/kernel/apic (#819)",
          "timestamp": "2026-11-10T14:07:40+08:00",
          "tree_id": "eca9c9d4208c3465bc5d3c18406b565c409a7b35",
          "url": "https://github.com/asterinas/vostd/commit/7d4224a4e0cf102ab78f8df041c013aad40c98bf"
        },
        "date": 1794291350878,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1025963410,
            "unit": "rlimit",
            "extra": "verified=4375 errors=0 smt-run=440,394ms wall=274,408ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 409862457,
            "unit": "rlimit",
            "extra": "smt-run=211,450ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 97497722,
            "unit": "rlimit",
            "extra": "smt-run=45,728ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 77978304,
            "unit": "rlimit",
            "extra": "smt-run=32,014ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,548ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,755ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,810ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,042ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=921ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=783ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d645ffcca81f44449f34d0b7a01902ce3bb60dbc",
          "message": "Update README.md (#901)",
          "timestamp": "2026-11-10T14:43:39+08:00",
          "tree_id": "d3e42e9e18b3c6310d5d1c68c90c0d4597b6d453",
          "url": "https://github.com/asterinas/vostd/commit/d645ffcca81f44449f34d0b7a01902ce3bb60dbc"
        },
        "date": 1794293366880,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1025963410,
            "unit": "rlimit",
            "extra": "verified=4375 errors=0 smt-run=400,731ms wall=252,565ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 409862457,
            "unit": "rlimit",
            "extra": "smt-run=196,666ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 97497722,
            "unit": "rlimit",
            "extra": "smt-run=43,746ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 77978304,
            "unit": "rlimit",
            "extra": "smt-run=32,666ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=1,967ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,444ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=874ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=735ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=661ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,316ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "64428fa0f4d3366172d686319b2fe64a44f2fb4f",
          "message": "chore: delete some redundant fields in ghost structs (#902)\n\n* chore: remove some dead field\n\n* Update virt_mem.rs",
          "timestamp": "2026-11-10T15:49:25+08:00",
          "tree_id": "d1498682b98ef9a71a35f081c1026a3a5a998a04",
          "url": "https://github.com/asterinas/vostd/commit/64428fa0f4d3366172d686319b2fe64a44f2fb4f"
        },
        "date": 1794297366074,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1134164723,
            "unit": "rlimit",
            "extra": "verified=4375 errors=0 smt-run=310,345ms wall=208,707ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 412898007,
            "unit": "rlimit",
            "extra": "smt-run=137,120ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 216784574,
            "unit": "rlimit",
            "extra": "smt-run=32,291ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 98034902,
            "unit": "rlimit",
            "extra": "smt-run=26,784ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=1,820ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,278ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,195ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=806ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=691ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=593ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "29f0517ec33a6a7423316b08de78664a83305d5d",
          "message": "chore: remove unused spec and proofs (#903)",
          "timestamp": "2026-11-10T16:21:01+08:00",
          "tree_id": "190673ae32c89feeced1d1c754cba4d73110ba11",
          "url": "https://github.com/asterinas/vostd/commit/29f0517ec33a6a7423316b08de78664a83305d5d"
        },
        "date": 1794299297961,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1126423808,
            "unit": "rlimit",
            "extra": "verified=4359 errors=0 smt-run=438,591ms wall=280,977ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 412898007,
            "unit": "rlimit",
            "extra": "smt-run=202,396ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 216784574,
            "unit": "rlimit",
            "extra": "smt-run=47,785ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 98034902,
            "unit": "rlimit",
            "extra": "smt-run=34,592ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,596ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,942ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,138ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=1,012ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=791ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,736ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "24317fd3c8b086a637c239cf7c9f426b3c7e368d",
          "message": "prove: several Debug Impls (#904)\n\n* prove: several Debug impls\n\n* Update mutex.rs\n\n* more\n\n* Update fmt.rs",
          "timestamp": "2026-11-10T16:59:19+08:00",
          "tree_id": "e6a30c4936f839fb39f329142d439ffd704a0967",
          "url": "https://github.com/asterinas/vostd/commit/24317fd3c8b086a637c239cf7c9f426b3c7e368d"
        },
        "date": 1794301727600,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1142722738,
            "unit": "rlimit",
            "extra": "verified=4367 errors=0 smt-run=472,606ms wall=299,511ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 428357402,
            "unit": "rlimit",
            "extra": "smt-run=233,195ms"
          },
          {
            "name": "rlimit: mm::frame::linked_list",
            "value": 216795755,
            "unit": "rlimit",
            "extra": "smt-run=40,057ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 88947765,
            "unit": "rlimit",
            "extra": "smt-run=36,893ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,379ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,873ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,504ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,078ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 2036235,
            "unit": "rlimit",
            "extra": "smt-run=869ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=709ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "db6611b8066458efe90f0bce701cccfd046ea833",
          "message": "fix: NonNullPtr (#897)\n\n* use `NonNullPtr` in `sync`\n\n* remove `NonNullPtrRef`\n\n* minor\n\n* minor\n\n* add Inv back\n\n* Update frame_ref.rs\n\n* add Inv\n\n* minor",
          "timestamp": "2026-11-10T21:36:54+08:00",
          "tree_id": "f52baeef64dad9984d863679e926e37ac63a8222",
          "url": "https://github.com/asterinas/vostd/commit/db6611b8066458efe90f0bce701cccfd046ea833"
        },
        "date": 1794318248817,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 971836089,
            "unit": "rlimit",
            "extra": "verified=4368 errors=0 smt-run=360,132ms wall=239,659ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 398510715,
            "unit": "rlimit",
            "extra": "smt-run=175,699ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=29,485ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=23,350ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,472ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,736ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,624ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=984ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=795ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=918ms"
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
          "id": "b8a1a753a88c9a0283b48c323754db37b8497684",
          "message": "prove: ktest in sync::mutex (#907)",
          "timestamp": "2026-11-11T11:16:58+08:00",
          "tree_id": "a63189b6463c0970cbb35604c32f489c99cc1e2c",
          "url": "https://github.com/asterinas/vostd/commit/b8a1a753a88c9a0283b48c323754db37b8497684"
        },
        "date": 1794368063453,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 971856753,
            "unit": "rlimit",
            "extra": "verified=4369 errors=0 smt-run=279,262ms wall=192,473ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 398510715,
            "unit": "rlimit",
            "extra": "smt-run=139,003ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=21,825ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=17,664ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=1,644ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,272ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,109ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=748ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=591ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=629ms"
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
          "id": "e306e100d72da95498ff2736d0a230e9f4ae65e1",
          "message": "dashboard: update Verified lines of code over time (#910)",
          "timestamp": "2026-11-11T14:08:38+08:00",
          "tree_id": "8115c9b092374e09030fe0debd70ea5e8548da08",
          "url": "https://github.com/asterinas/vostd/commit/e306e100d72da95498ff2736d0a230e9f4ae65e1"
        },
        "date": 1794377716595,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945705530,
            "unit": "rlimit",
            "extra": "verified=4371 errors=0 smt-run=376,684ms wall=253,590ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373566813,
            "unit": "rlimit",
            "extra": "smt-run=178,886ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=29,712ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=25,089ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,553ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,782ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,607ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,082ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=817ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=923ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "9cfb1101637d56acd005133c4dab391bb4214936",
          "message": "fix: remove VmSpace lifetime (#911)\n\n* fix: remove VmSpace lifetime generic\n\n* fix error reexport\n\n* fmt",
          "timestamp": "2026-11-11T14:39:59+08:00",
          "tree_id": "777447c5213a57be73a56982c99508fb6e84f40c",
          "url": "https://github.com/asterinas/vostd/commit/9cfb1101637d56acd005133c4dab391bb4214936"
        },
        "date": 1794379597728,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945785489,
            "unit": "rlimit",
            "extra": "verified=4371 errors=0 smt-run=348,607ms wall=234,103ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373566813,
            "unit": "rlimit",
            "extra": "smt-run=165,067ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=24,475ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=23,009ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=2,539ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,782ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,603ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=975ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=759ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=897ms"
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
          "id": "6295299f34fedf630fc371a6a23e9081758dd262",
          "message": "dashboard: optimize verified lines plot (#912)\n\n* dashboard: optimize verified lines plot\n\n* dashboard: time as x-axis for verified lines",
          "timestamp": "2026-11-11T14:54:55+08:00",
          "tree_id": "db8f4ee5af6c10cc4cf894aa10b852fa613d05a2",
          "url": "https://github.com/asterinas/vostd/commit/6295299f34fedf630fc371a6a23e9081758dd262"
        },
        "date": 1794381762189,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945785489,
            "unit": "rlimit",
            "extra": "verified=4371 errors=0 smt-run=273,999ms wall=193,782ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373566813,
            "unit": "rlimit",
            "extra": "smt-run=131,459ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=23,699ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=13,838ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8778479,
            "unit": "rlimit",
            "extra": "smt-run=1,751ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,379ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=753ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=589ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=649ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,163ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "95096031+alpha-beta-eta@users.noreply.github.com",
            "name": "alpha-beta-eta",
            "username": "alpha-beta-eta"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b0d0d3d4deedb419caf7b6b338aa9a100cba8e41",
          "message": "ci: add ensures-coverage, an advisory postcondition check (#913)",
          "timestamp": "2026-11-11T17:53:02+08:00",
          "tree_id": "86e7dd9c6699c91ad542b6fbb6b324ad33419422",
          "url": "https://github.com/asterinas/vostd/commit/b0d0d3d4deedb419caf7b6b338aa9a100cba8e41"
        },
        "date": 1794392094316,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945689033,
            "unit": "rlimit",
            "extra": "verified=4373 errors=0 smt-run=289,219ms wall=203,802ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=138,133ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=25,614ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=18,721ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=1,810ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,311ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,207ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=805ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=629ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=650ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "b6db6df974cf0af881255cf88613836613fc6ce4",
          "message": "Verify bzImage address mappings (#915)\n\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-12T10:49:59+08:00",
          "tree_id": "4c7165490ef71fee78777fef778fa6251ed42f2a",
          "url": "https://github.com/asterinas/vostd/commit/b6db6df974cf0af881255cf88613836613fc6ce4"
        },
        "date": 1794453293618,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945689033,
            "unit": "rlimit",
            "extra": "verified=4373 errors=0 smt-run=293,797ms wall=203,088ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=141,884ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=22,072ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=19,898ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=1,738ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,324ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,162ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=770ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=619ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=623ms"
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
          "id": "7dca80845ef30e69bb19cfe7293f9bfa5fc3d3a2",
          "message": "docs: update coding guidelines for comments and spec check (#917)\n\n* docs: update coding guidelines for comments\n\n* docs: spec check\n\n* doc: update",
          "timestamp": "2026-11-12T14:07:32+08:00",
          "tree_id": "4281b3ad9be056c4878675f57eb8f0ba907d801a",
          "url": "https://github.com/asterinas/vostd/commit/7dca80845ef30e69bb19cfe7293f9bfa5fc3d3a2"
        },
        "date": 1794464655372,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945689111,
            "unit": "rlimit",
            "extra": "verified=4373 errors=0 smt-run=303,729ms wall=216,861ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=137,498ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=26,873ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=16,505ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=2,125ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,464ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,347ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=932ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=664ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=744ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "35a5722f5a802ac0f594d780306f61afa9f37370",
          "message": "Verify x86 TSC frequency calculation via CPUID (#905)\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-12T14:38:52+08:00",
          "tree_id": "1a412723f7ab474ef4640533c92d856fc177e223",
          "url": "https://github.com/asterinas/vostd/commit/35a5722f5a802ac0f594d780306f61afa9f37370"
        },
        "date": 1794465975637,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945774166,
            "unit": "rlimit",
            "extra": "verified=4375 errors=0 smt-run=325,926ms wall=229,585ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=154,710ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=28,110ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=16,938ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=2,162ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,539ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,444ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=942ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=678ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=852ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "157275997+YuQuuu@users.noreply.github.com",
            "name": "YuQuuu",
            "username": "YuQuuu"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "30581d3014f3ddf537d406f997ddc3abe416b514",
          "message": "prove: verify ostd-test initialization and formatting (#918)\n\n* Prove ostd-test iterator initialization and formatting\n\n* Count ostd-test in verification coverage\n\n* Remove redundant verification overview",
          "timestamp": "2026-11-12T16:56:31+08:00",
          "tree_id": "5f0d780120037648088ba94f305a36ccf21ecdd9",
          "url": "https://github.com/asterinas/vostd/commit/30581d3014f3ddf537d406f997ddc3abe416b514"
        },
        "date": 1794474275716,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 945774166,
            "unit": "rlimit",
            "extra": "verified=4375 errors=0 smt-run=423,005ms wall=272,521ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=208,756ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=31,489ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=28,800ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=2,672ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,844ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,792ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,061ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=733ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=923ms"
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
          "id": "6e20764d1cf4006b193ace48e4afcff59517badb",
          "message": "Verify RCU Either tests and centralize layout specs (#909)",
          "timestamp": "2026-11-12T21:34:21+08:00",
          "tree_id": "60cf72f7365786e8ea7da0dba23ea9cf66be4298",
          "url": "https://github.com/asterinas/vostd/commit/6e20764d1cf4006b193ace48e4afcff59517badb"
        },
        "date": 1794490971906,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 941239088,
            "unit": "rlimit",
            "extra": "verified=4387 errors=0 smt-run=477,097ms wall=307,504ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=230,545ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=39,454ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=34,202ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=2,773ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=2,109ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=2,199ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,317ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=795ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=1,066ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "etyyuiope@qq.com",
            "name": "Hiroki Chen",
            "username": "hiroki-chen"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "d079460c09249fe2be21b4fa4fe0559a44c372fa",
          "message": "Remove RCU read-token assumptions with real fractions and a pool registry (#922)\n\nThe default `Rcu` proof relied on six `assume`s:\n\n- `load_read_token` assumed the bounded `CountResource` reader pool never\n  ran out (`not_empty`, `1 < frac`).\n- `compare_exchange` and `drop` assumed (`assume(false)`) that a returned\n  read token always belongs to the current pool or a retired pool.\n\nReplace the integer-count reader pool with `vstd::resource::frac_opt::Frac`,\nwhose real-valued fractions can always be split, and drop the artificial\n`RCU_READER_SLOTS` bound.\n\nAdd a monotone per-cell pool registry (`GhostSetAuth<Loc>` with a persistent\nsubset). Every registered pool is either the current pool or retired, and each\nread token carries a persistent singleton witness of its pool's registration,\nso returning a token is now proved to hit a known pool. Fresh pool ids are\nshown distinct from existing ones via `Frac::bounded_with`.\n\nFactor the pool retire/publish step into `RcuPtrGhost::tracked_replace` and\nthe token return path into `tracked_return_token`. Executable code is\nunchanged; `RcuInner` gains only a ghost `pool_registry` field.\n\nCo-authored-by: Claude Opus 5.5 <noreply@anthropic.com>",
          "timestamp": "2026-11-12T19:41:19-05:00",
          "tree_id": "d6f353fe744cc3377a720385b401f19dcebd6079",
          "url": "https://github.com/asterinas/vostd/commit/d079460c09249fe2be21b4fa4fe0559a44c372fa"
        },
        "date": 1794531834006,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 941164853,
            "unit": "rlimit",
            "extra": "verified=4392 errors=0 smt-run=362,976ms wall=243,394ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=172,285ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=26,621ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=24,772ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=2,498ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,827ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,003ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=783ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=883ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,600ms"
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
          "id": "52715e6ecd70b2b8aeb48818f4274dcb4930e598",
          "message": "ci: split stats from pages action and count test code (#925)\n\n* ci: split stats from pages action and count test code\n\n* ci: simplify\n\n* fix: error in PR CI\n\n* ci: always upload verified API",
          "timestamp": "2026-11-13T16:29:17+08:00",
          "tree_id": "3af815c412606d690876a1c17aea28fc4e624b11",
          "url": "https://github.com/asterinas/vostd/commit/52715e6ecd70b2b8aeb48818f4274dcb4930e598"
        },
        "date": 1794558991563,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 941164853,
            "unit": "rlimit",
            "extra": "verified=4392 errors=0 smt-run=249,739ms wall=174,431ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 373645598,
            "unit": "rlimit",
            "extra": "smt-run=124,773ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83275612,
            "unit": "rlimit",
            "extra": "smt-run=22,874ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53622018,
            "unit": "rlimit",
            "extra": "smt-run=13,504ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=1,328ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,080ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=923ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=654ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=505ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=528ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "64517311+rikosellic@users.noreply.github.com",
            "name": "Xinyi Wan",
            "username": "rikosellic"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "46440af7206dc3132253ebb8cb5e190a5d711e76",
          "message": "chore: align import with source code (#926)\n\n* reorder import\n\n* Update segment.rs\n\n* update page_table/mod.rs\n\n* update cursor/mod.rs\n\n* update child.rs\n\n* update entry.rs\n\n* update node/mod.rs\n\n* fmt\n\n* fmt\n\n* fmt\n\n* Update mod.rs",
          "timestamp": "2026-11-13T17:21:26+08:00",
          "tree_id": "bd38984b48cbefd0af948108fe087bf755792877",
          "url": "https://github.com/asterinas/vostd/commit/46440af7206dc3132253ebb8cb5e190a5d711e76"
        },
        "date": 1794562486460,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 959818563,
            "unit": "rlimit",
            "extra": "verified=4392 errors=0 smt-run=309,038ms wall=211,897ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 392002662,
            "unit": "rlimit",
            "extra": "smt-run=156,277ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83288148,
            "unit": "rlimit",
            "extra": "smt-run=24,731ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53624162,
            "unit": "rlimit",
            "extra": "smt-run=17,542ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=1,931ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,321ms"
          },
          {
            "name": "rlimit: utf8",
            "value": 4218520,
            "unit": "rlimit",
            "extra": "smt-run=1,232ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=814ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=598ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=668ms"
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
          "id": "90087275ebd4b974596947d11d3da27d722e05d3",
          "message": "prove: mm ktests with strengthened VmReader/VmWriter contracts (#924)\n\n* prove: ktest in mm\n\n* stats: count test code as the verified code\n\n* refine\n\n* refine and doc",
          "timestamp": "2026-11-13T17:44:51+08:00",
          "tree_id": "c370301db95574852e2de0ebaff63fcb265ed77f",
          "url": "https://github.com/asterinas/vostd/commit/90087275ebd4b974596947d11d3da27d722e05d3"
        },
        "date": 1794563614864,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 961567225,
            "unit": "rlimit",
            "extra": "verified=4406 errors=0 smt-run=250,575ms wall=173,110ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 392002662,
            "unit": "rlimit",
            "extra": "smt-run=120,415ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 83288148,
            "unit": "rlimit",
            "extra": "smt-run=21,795ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 53624162,
            "unit": "rlimit",
            "extra": "smt-run=16,417ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=1,567ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,273ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=724ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=499ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=551ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,005ms"
          }
        ]
      },
      {
        "commit": {
          "author": {
            "email": "liudugang@szu.edu.cn",
            "name": "DID-Lab-SZU",
            "username": "DID-Lab-SZU"
          },
          "committer": {
            "email": "noreply@github.com",
            "name": "GitHub",
            "username": "web-flow"
          },
          "distinct": true,
          "id": "41ccd7463895815f6d59fe53eb4157affabb13e3",
          "message": "prove: remove paging layout axiom and refactor architecture specs (#855)\n\n* Remove paging layout axiom and generalize page-table levels\n\n* Format paging specifications with the CI formatter\n\nApply the exact formatting changes reported by PR #855 CI using verusfmt 0.7.4. Repeated make fmt produces no further changes.\n\nValidation: make; repeated make fmt; git diff --check.\n\n* Reduce page-table cursor verification cost\n\nLocalize quantified invariant unfolding in cursor scans, jumps, and maps.\nIsolate mapping disjointness and same-slot address preservation proofs in\nseparate solver contexts, and narrow the page-table invariant expansion\nneeded when restoring a parent continuation.\n\nAfter rebasing onto upstream/main 90087275e, reduce OSTD rlimit from\n1,193,093,450 to 1,011,602,095. The full CI-equivalent total is\n1,087,033,549, 13.0% above the latest main baseline and below the 20%\nperformance alert threshold. Preserve cursor contracts and executable\nbehavior.\n\nValidation: make; x86_64 full verification with --time-expanded;\nmake verify-riscv; make verify-loongarch; repeated make fmt;\ngit diff --check. The local regression module and incremental=false\nconfiguration remain excluded from this commit.\n\n* Address paging contract review feedback\n\n---------\n\nCo-authored-by: uuu <3100141307@qq.com>",
          "timestamp": "2026-11-14T13:15:42+08:00",
          "tree_id": "dcebf496a9da1e8e3e8a9832296100e2b9479e1e",
          "url": "https://github.com/asterinas/vostd/commit/41ccd7463895815f6d59fe53eb4157affabb13e3"
        },
        "date": 1794634463294,
        "tool": "customSmallerIsBetter",
        "benches": [
          {
            "name": "total rlimit",
            "value": 1162145083,
            "unit": "rlimit",
            "extra": "verified=4462 errors=0 smt-run=433,613ms wall=268,558ms"
          },
          {
            "name": "rlimit: mm::page_table::cursor",
            "value": 446938691,
            "unit": "rlimit",
            "extra": "smt-run=204,525ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::cursor_steps",
            "value": 166169056,
            "unit": "rlimit",
            "extra": "smt-run=51,749ms"
          },
          {
            "name": "rlimit: specs::mm::page_table::cursor::mapping_set_lemmas",
            "value": 86630488,
            "unit": "rlimit",
            "extra": "smt-run=34,613ms"
          },
          {
            "name": "rlimit: seq_lib",
            "value": 8677157,
            "unit": "rlimit",
            "extra": "smt-run=2,488ms"
          },
          {
            "name": "rlimit: arithmetic::div_mod",
            "value": 7914703,
            "unit": "rlimit",
            "extra": "smt-run=1,890ms"
          },
          {
            "name": "rlimit: temporal_logic::rules",
            "value": 3164776,
            "unit": "rlimit",
            "extra": "smt-run=1,018ms"
          },
          {
            "name": "rlimit: bits",
            "value": 2027793,
            "unit": "rlimit",
            "extra": "smt-run=800ms"
          },
          {
            "name": "rlimit: ghost_tree",
            "value": 1928188,
            "unit": "rlimit",
            "extra": "smt-run=906ms"
          },
          {
            "name": "rlimit: arithmetic::internals::mod_internals",
            "value": 1451900,
            "unit": "rlimit",
            "extra": "smt-run=1,563ms"
          }
        ]
      }
    ]
  }
}