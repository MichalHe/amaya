# Technical description of Amaya

`amaya.tex` (16 pages) is a reference description of how the solver works: components, algorithms,
configuration options, and the measurements that exist. It is written from the source at commit
`b3fc4d3` (branch `devel`) and is intended both as documentation and as source material for a later
academic paper.

## Contents

| § | Topic |
|---|---|
| 1 | Purpose, scope, conventions (what the document is based on, how code is referenced) |
| 2 | Decision procedure: encoding, atom types and their state spaces, operations |
| 3 | Component overview and execution stages |
| 4 | Front end: normalisation sequence, variable identity, non-linear terms, typed AST, structural ids |
| 5 | The 20 registered optimisation passes: what each matches and produces, with side conditions |
| 6 | Pass coordination: the legacy 18-step sequence and the opt-in fixpoint scheduler |
| 7 | Evaluation core: node handlers, conjunct reordering, projection order, minimisation points, sharding |
| 8 | Automata back ends: native; MTBDD representation, operations as applies, padding closure, minimisation, memory/interruption |
| 9 | Specialised constructions: lazy construction, bounded congruence, automaton cache, top-level SAT |
| 10 | Configuration surface: CLI options → config fields, driver modes |
| 11 | Recorded measurements (SMT-COMP 2025) |
| 12 | Test and validation infrastructure |
| 13 | Current limitations |
| 14 | Measurements not currently available |
| 15 | Index of the design documents in the repository |

## Building

```sh
pdflatex amaya && pdflatex amaya      # second run resolves \ref/\label
```

Requires a stock TeX Live (article class + amsmath, booktabs, tikz, hyperref, listings). Builds with
no overfull boxes and no unresolved references.

## Reproducing the numbers in §11

```sh
./data/smtcomp25_tables.py            # human-readable summary
./data/smtcomp25_tables.py --latex    # the LaTeX table bodies used in the document
```

The script reads `../smtcomp25-results/results-sq-2025.json` (the published SMT-COMP 2025 single-query
dump) and recomputes solved counts, PAR-2, median solve times, per-family breakdowns, uniquely-solved
instances and virtual-best-solver contributions. It runs no solver. Definitions are in its docstring.

Summary of what §11 records:

| | LIA (300) | NIA (254) |
|---|---|---|
| Amaya solved | 190 (4th of 8) | 208 (4th of 8) |
| unsolved: timeout / OOM / unknown | 12 / 93 / 5 | 6 / 0 / 40 |
| uniquely solved | 53 (all `20250213-Frobenius`) | 0 |
| VBS with / without Amaya | 287 / 234 | 249 / 249 |

## Using this as the basis for a paper

Two sections exist specifically for that purpose:

- **§14 (Measurements not currently available)** lists what a publication would have to measure and
  what is currently unquantified: per-pass ablation, scheduler-vs-legacy parity, back-end
  micro-benchmarks, automaton cache hit rate, attribution of the 93 LIA out-of-memory results to
  specific operations, and comparison against other automata-based tools (LASH, MONA).
- **§15** indexes the in-repository design documents (`OPTIMIZATION_PIPELINE.md`, `SAT_TOP_LEVEL.md`,
  `DEBRUJIN_CSE.md`, …), which contain the derivations this document summarises.

Other things a paper draft would need and that this document deliberately does not contain: an
abstract, related-work positioning with citations (`refs.bib` holds unverified skeleton entries),
author affiliation, and an availability statement with a repository URL and licence.
