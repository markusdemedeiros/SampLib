# Core

This directory holds the spec interfaces beyond `IsDistSpec`, helpers for closed terms, lists, and arrays, and a proof-mode extension. Every family builds on it.

For how the directories fit together, see the [library layout](../README.md#layout).

## Contents

- Top level: 17 modules
- [`Laws/`](Laws): 3 modules with target laws, kernels, and expectation lemmas
- [`Syntax/`](Syntax): 5 modules with unfolding lemmas for the `pl%` source terms

---

`python3 agent-scripts/law_index.py` generates this file.
