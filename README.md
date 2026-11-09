# Proximity gaps for expander codes

Lean 4 formalization of distance, smoothness, and proximity gaps for expander
codes. Companion to
[*On Proximity Gaps for Expander Codes*](https://eprint.iacr.org/2026/2806) (ePrint 2026/2806).

Start with [the main theorems](LDPC/Theorems/Main.lean).
[Paper statements](LDPC/Theorems/Paper.lean) include the Ligero test, sampling
constraints, and an additional hybrid sampling corollary.

- [Statements](LDPC/Statements): definitions and verifier contracts.
- [Paper lemmas](LDPC/PaperLemmas) and [helpers](LDPC/Helpers): supporting proofs.
- [Review entry point](LDPC/Statements/Review.lean): declaration index.

With [elan](https://github.com/leanprover/elan) installed:

```sh
lake exe cache get
lake build LDPC LDPC.Statements.Review
```

The toolchain and dependencies are pinned in the repository.
