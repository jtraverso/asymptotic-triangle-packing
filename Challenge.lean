/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib

/-!
# Near-regular hypergraph matchings and the asymptotic triangle-packing gap

Four statements are formalized.

1. **A finite nibble theorem** (`near_regular_nibble`). For every `r ≥ 2` and `β > 0` there are
   `μ, η, d₀ > 0` such that every `r`-uniform hypergraph `H` on a finite vertex set `V` with a
   degree scale `d ≥ d₀` such that
   * all vertices outside an exceptional set of at most `η|V|` vertices have degree at least
     `(1 - μ) d`,
   * every vertex has degree at most `(1 + μ) d`, and
   * any two distinct vertices lie together in at most `μ d` edges,

   has a matching (pairwise disjoint edges of `H`) with at least `(1 - β) |V| / r` edges.

2. **Fractional versus integral triangle packing** (`fractional_triangle_packing_gap`). For every
   `ε > 0`, every large enough finite graph `G` on `n` vertices has an edge-disjoint family `P` of
   triangles such that every fractional triangle packing of `G` has total weight at most
   `|P| + ε n²`. (Haxell–Rödl, for triangles: `ν*(G) - ν(G) = o(n²)`.)

3. **Fractional triangle cover versus integral packing** (`triangle_cover_packing_gap`). For every
   `ε > 0`, every large enough finite graph `G` on `n` vertices has an edge-disjoint family `P` of
   triangles and a fractional triangle cover of `G` of total weight at most `|P| + ε n²`.

4. **Approximate decompositions from fractional ones** (`approx_decomposition_of_fractional`,
   version 2). For every `η > 0`, every large enough finite graph on `n` vertices with a fractional
   triangle decomposition (weights on triangles summing to exactly one at every edge) has an
   edge-disjoint triangle family covering all but at most `η n²` of its edges (Haxell–Rödl,
   transfer form, for triangles).

A triangle is a 3-element vertex set inducing a clique (`G.cliqueFinset 3`); the edges of `G`
inside a vertex set `t` are `edgesIn G t`. Two triangles are edge-disjoint when they share at most
one vertex.

The Mathlib definitions used in these statements are reproduced verbatim, with file and line at the
pinned Mathlib revision, in `MATHLIB_DEFINITIONS.md` at the root of this repository.
-/

@[expose] public section

open SimpleGraph Finset

namespace AsymptoticTrianglePacking

/-- The edges of `G` with both endpoints in the vertex set `t`. -/
def edgesIn {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (t : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter fun e => ∀ v ∈ e, v ∈ t

/-- An (integral) triangle packing of `G`: a family of triangles of `G`, any two of which share
at most one vertex, i.e. no edge. -/
def IsTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (P : Finset (Finset V)) : Prop :=
  P ⊆ G.cliqueFinset 3 ∧ ∀ s ∈ P, ∀ t ∈ P, s ≠ t → #(s ∩ t) ≤ 1

/-- A fractional triangle packing of `G`: nonnegative weights on vertex sets such that, for every
edge `e` of `G`, the triangles of `G` containing `e` have total weight at most one. -/
def IsFracTrianglePacking {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t ≤ 1

/-- A fractional triangle cover of `G`: nonnegative weights on unordered pairs such that, for
every triangle `t` of `G`, the edges of `G` inside `t` have total weight at least one. -/
def IsFracTriangleCover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (y : Sym2 V → ℝ) : Prop :=
  (∀ e, 0 ≤ y e) ∧ ∀ t ∈ G.cliqueFinset 3, 1 ≤ ∑ e ∈ edgesIn G t, y e

/-- A fractional triangle decomposition of `G`: nonnegative weights on vertex sets such that, for
every edge `e` of `G`, the triangles of `G` containing `e` have total weight exactly one. -/
def IsFracTriangleDecomp {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : Finset V → ℝ) : Prop :=
  (∀ t, 0 ≤ w t) ∧ ∀ e ∈ G.edgeFinset, ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t = 1

/-- **A finite near-regular nibble theorem.** Uniform hypergraphs whose degrees are at most
`(1 + μ) d` everywhere and at least `(1 - μ) d` outside a set of at most `η |V|` vertices, and whose
codegrees are at most `μ d`, have matchings covering all but a `β`-fraction of the vertices. -/
theorem near_regular_nibble (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ η : ℝ, 0 < η ∧ ∃ d₀ : ℝ, 0 < d₀ ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] (H : Finset (Finset V)) (d : ℝ), d₀ ≤ d →
        (∀ e ∈ H, #e = r) →
        (∃ X : Finset V, (#X : ℝ) ≤ η * Fintype.card V ∧
          ∀ v ∉ X, (1 - μ) * d ≤ (#{e ∈ H | v ∈ e} : ℝ)) →
        (∀ v : V, (#{e ∈ H | v ∈ e} : ℝ) ≤ (1 + μ) * d) →
        (∀ x y : V, x ≠ y → (#{e ∈ H | x ∈ e ∧ y ∈ e} : ℝ) ≤ μ * d) →
        ∃ M ⊆ H, (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
          (1 - β) * ((Fintype.card V : ℝ) / r) ≤ (#M : ℝ) := by
  sorry

/-- **The fractional–integral triangle-packing gap is `o(n²)`.** For every `ε > 0`, every large
enough finite graph has an edge-disjoint triangle family `P` with `ν*(G) ≤ |P| + ε n²`. -/
theorem fractional_triangle_packing_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        ∃ P : Finset (Finset V), IsTrianglePacking G P ∧
          ∀ w : Finset V → ℝ, IsFracTrianglePacking G w →
            ∑ t ∈ G.cliqueFinset 3, w t ≤ (#P : ℝ) + ε * (Fintype.card V : ℝ) ^ 2 := by
  sorry

/-- **The fractional cover–integral packing gap for triangles is `o(n²)`.** For every `ε > 0`,
every large enough finite graph has an edge-disjoint triangle family `P` and a fractional triangle
cover of total weight at most `|P| + ε n²`. -/
theorem triangle_cover_packing_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        ∃ P : Finset (Finset V), ∃ y : Sym2 V → ℝ, IsTrianglePacking G P ∧
          IsFracTriangleCover G y ∧
            ∑ e ∈ G.edgeFinset, y e ≤ (#P : ℝ) + ε * (Fintype.card V : ℝ) ^ 2 := by
  sorry

/-- **Haxell–Rödl, transfer form, for triangles.** For every `η > 0`, every large enough finite
graph `G` on `n` vertices that has a fractional triangle decomposition has an edge-disjoint triangle
family covering all edges of `G` except at most `η n²`. -/
theorem approx_decomposition_of_fractional (η : ℝ) (hη : 0 < η) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V → (∃ w : Finset V → ℝ, IsFracTriangleDecomp G w) →
        ∃ P : Finset (Finset V), IsTrianglePacking G P ∧
          (#(G.edgeFinset \ P.biUnion (edgesIn G)) : ℝ) ≤ η * (Fintype.card V : ℝ) ^ 2 := by
  sorry

end AsymptoticTrianglePacking
