window.BENCHMARK_DATA = {
  "lastUpdate": 1792939457516,
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
      }
    ]
  }
}