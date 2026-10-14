# Near-regular hypergraph matchings and the asymptotic triangle-packing gap in Lean 4

Author and maintainer: **Juan Pablo Traverso Gianini**. Licence: Apache-2.0 (see `LICENSE`).

This repository formalizes three results.

1. **A finite near-regular nibble theorem.** For every `r ≥ 2` and `β > 0` there are
   `μ, η, d₀ > 0` with the following property. Let `H` be an `r`-uniform hypergraph on a finite
   vertex set `V` and let `d ≥ d₀`. Suppose that:
   - every vertex has degree at most `(1 + μ) d`;
   - all vertices outside an exceptional set of at most `η |V|` vertices have degree at least
     `(1 − μ) d`;
   - any two distinct vertices lie together in at most `μ d` edges.

   Then `H` has a matching with at least `(1 − β) |V| / r` edges. This is a variant of the
   Frankl–Rödl / Pippenger–Spencer nibble theorem. It tolerates a small set of low-degree
   vertices, but requires the degree ceiling everywhere.
2. **Fractional vs. integral triangle packing.** For every `ε > 0`, every large enough finite
   graph `G` on `n` vertices has a family `P` of edge-disjoint triangles such that every
   fractional triangle packing of `G` has total weight at most `|P| + ε n²`. That is,
   `ν*(G) − ν(G) = o(n²)` uniformly, the triangle case of the Haxell–Rödl theorem.
3. **Fractional triangle cover vs. integral packing.** For every `ε > 0`, every large enough finite
   graph on `n` vertices has a family `P` of edge-disjoint triangles and a fractional triangle
   cover of total weight at most `|P| + ε n²`. That is, `τ*(G) − ν(G) = o(n²)`.

The audited statements are in [`Challenge.lean`](Challenge.lean), which imports only Mathlib. The
proofs are in [`Solution.lean`](Solution.lean). Supporting files:
- [`comparator.json`](comparator.json) names the compared theorems;
- [`MATHLIB_DEFINITIONS.md`](MATHLIB_DEFINITIONS.md) reproduces verbatim the Mathlib definitions
  used;
- [`formalization.yaml`](formalization.yaml) records provenance, sources and process.

## How the proof goes

* **Nibble.** A random greedy ("nibble") process runs in rounds. Its one-round estimates are
  controlled by second moments and a Freedman-type martingale inequality. A schedule of rounds
  keeps the hypergraph near-regular outside a small exceptional set, and a final greedy step
  absorbs the leftover. The code is in `LeanPool/AsymptoticTrianglePacking/Internal/`
  (`Tight/`, `TightSchedule.lean`, `WeightedBoundedEdges.lean`, `RegularMost.lean`).
* **Triangle-packing gap.** The triangles of `G` form a 3-uniform hypergraph on the edges of `G`,
  with codegree at most one. Its matchings are the edge-disjoint triangle families.
  1. A low-degree core reduction deletes few edges and leaves every vertex isolated or of linear
     degree.
  2. The dense regime is settled by the nibble.
  3. The remaining regimes are reduced with Mathlib's Szemerédi regularity lemma to a cluster
     linear program on the reduced graph, rounded by explicit grid and box designs.

  This is in `Internal/AX1/`.
* **Cover form.** LP duality `τ* = ν*` gives the cover form (`Internal/AX1/CoreGapAX1.lean`).
  `Solution.lean` adds two bridges:
  - a maximum edge-disjoint family realizes `ν`, and a cover within `ε n² / 2` of the infimum
    `τ*` exists;
  - weak duality between fractional packings and covers.

The modules under `LeanPool/` are the author's contribution to
[Lean Pool](https://github.com/LeanPool/lean-pool) (PRs #544 and #471). They are copied from
Lean Pool commit `26ce45d3871e5560a8baffa4d49a8942b1d20a24`, with the copyright and author header
lines normalized to the maintainer's name.

## Sources

* P. E. Haxell, V. Rödl, *Integer and fractional packings in dense graphs*, Combinatorica 21
  (2001) 13–38, doi:10.1007/s004930170003.
* R. Yuster, *Integer and fractional packing of families of graphs*, Random Structures &
  Algorithms 26 (2005) 110–118, doi:10.1002/rsa.20048.
* P. Frankl, V. Rödl, *Near perfect coverings in graphs and hypergraphs*, European J. Combin. 6
  (1985) 317–326, doi:10.1016/S0195-6698(85)80045-7.
* N. Pippenger, J. Spencer, *Asymptotic behavior of the chromatic index for hypergraphs*, J.
  Combin. Theory Ser. A 51 (1989) 24–42, doi:10.1016/0097-3165(89)90074-5.
* J. P. Traverso Gianini, Paper III of the preprint series
  [erdos-81-chordal-clique-partitions](https://github.com/jtraverso/erdos-81-chordal-clique-partitions/tree/main/preprints/PAPER_III).
  This Lean development was built for it.

## Authorship and use of AI

The results, the statements and the proof route were chosen by the author. The Lean proofs were
produced with AI assistance (Harmonic's Aristotle, and Claude in Claude Code for the packaging)
and checked mechanically with Lean. See `formalization.yaml`.

## Building

Lean `v4.35.0-rc3`, Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`:

```bash
lake exe cache get
lake build
```
