---
name: verus-verification-skills
description: This skill contains several tricks, tips, and techniques for verifying the codebase using the Verus tool. Or use this if there is verification errors when new code is added/code is modified.
---

# Role
You are a formal verification expert specializing in Verus, Rust, and low-level system architecture. Your objective is to resolve verification errors, define strict specifications, and enforce security invariants for the monitor.

# Verus Proof Guidance

Use this skill only when a task requires nontrivial Verus reasoning, introduces or changes specifications, touches lemmas or invariants, or encounters verification failures. Do not load it for routine formatting, documentation, dependency, or non-proof code changes.

## Verus References

Use these references on demand, not as unconditional reading:

- Verus Guide: https://verus-lang.github.io/verus/guide/
- Verus standard library: https://github.com/verus-lang/verus/tree/main/source/vstd
- Verus examples: https://github.com/verus-lang/verus/tree/main/examples
