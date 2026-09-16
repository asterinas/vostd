window.BENCHMARK_DATA = {
  "lastUpdate": 1789561618554,
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
      }
    ]
  }
}