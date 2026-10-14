/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib
public import LeanPool.AsymptoticTrianglePacking

/-!
# Proofs of the statements in `Challenge.lean`

The definitions below are verbatim copies of those in `Challenge.lean`. The three theorems are
derived from the library's public theorems:

* `near_regular_nibble` is `LeanPool.AsymptoticTrianglePacking.nearRegularNibbleTheorem`, with the
  hypergraph degree, codegree and matching notions unfolded;
* `triangle_cover_packing_gap` follows from
  `LeanPool.AsymptoticTrianglePacking.triangleCoverPackingGap` (stated with the infimum `τ₃*` of
  the fractional triangle covers and the maximum `ν₃` of the edge-disjoint triangle families),
  applied with `ε / 2`: a maximum edge-disjoint family realizes `ν₃`, and a cover within
  `ε n² / 2` of the infimum exists;
* `fractional_triangle_packing_gap` follows from the cover statement by weak LP duality
  (`sum_le_of_packing_cover`).
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
  obtain ⟨μ, hμ, η, hη, d₀, hd₀, h⟩ :=
    LeanPool.AsymptoticTrianglePacking.nearRegularNibbleTheorem r hr β hβ
  refine ⟨μ, hμ, η, hη, d₀, hd₀, fun V _ _ H d hd hu hreg hceil hcod => ?_⟩
  obtain ⟨X, hX, hXr⟩ := hreg
  obtain ⟨M, hM, hMc⟩ := h H d (hd₀.trans_le hd) hd hu ⟨X, hX, fun v hv => ⟨hXr v hv, hceil v⟩⟩
    hcod hceil
  exact ⟨M, hM.subset, hM.disjoint, hMc⟩

/-- **Weak duality.** The total weight of a fractional triangle packing is at most the total
weight of any fractional triangle cover. -/
theorem sum_le_of_packing_cover {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {w : Finset V → ℝ} {y : Sym2 V → ℝ} (hw : IsFracTrianglePacking G w)
    (hy : IsFracTriangleCover G y) :
    ∑ t ∈ G.cliqueFinset 3, w t ≤ ∑ e ∈ G.edgeFinset, y e := by
  calc ∑ t ∈ G.cliqueFinset 3, w t
      ≤ ∑ t ∈ G.cliqueFinset 3, w t * ∑ e ∈ edgesIn G t, y e := by
        refine Finset.sum_le_sum fun t ht => ?_
        simpa using mul_le_mul_of_nonneg_left (hy.2 t ht) (hw.1 t)
    _ = ∑ t ∈ G.cliqueFinset 3, ∑ e ∈ G.edgeFinset,
          if e ∈ edgesIn G t then w t * y e else 0 := by
        refine Finset.sum_congr rfl fun t _ => ?_
        have hsub : edgesIn G t ⊆ G.edgeFinset := by
          intro x hx
          unfold edgesIn at hx
          exact (Finset.mem_filter.1 hx).1
        rw [Finset.mul_sum, Finset.sum_ite_mem, Finset.inter_eq_right.2 hsub]
    _ = ∑ e ∈ G.edgeFinset, y e * ∑ t ∈ G.cliqueFinset 3 with e ∈ edgesIn G t, w t := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        split_ifs <;> ring
    _ ≤ ∑ e ∈ G.edgeFinset, y e * 1 :=
        Finset.sum_le_sum fun e he => mul_le_mul_of_nonneg_left (hw.2 e he) (hy.1 e)
    _ = ∑ e ∈ G.edgeFinset, y e := by simp

/-- A maximum matching of the edge-based triangle hypergraph gives an edge-disjoint triangle
family with `ν₃(G)` members. -/
theorem exists_packing_card_eq_nu3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] :
    ∃ P : Finset (Finset V), IsTrianglePacking G P ∧ #P = Nibble.YusterE.nu3 G := by
  classical
  set H := Nibble.YusterE.triangleHypergraphE G
  set S := H.powerset.filter (fun M => Hypergraph.IsMatching H M)
  have hS : S.Nonempty := ⟨∅, Finset.mem_filter.2
    ⟨Finset.empty_mem_powerset _, ⟨Finset.empty_subset _, by simp⟩⟩⟩
  obtain ⟨M, hMS, hMc⟩ := Finset.exists_mem_eq_sup S hS Finset.card
  have hnu : Nibble.YusterE.nu3 G = S.sup Finset.card := rfl
  have hM : Hypergraph.IsMatching H M := (Finset.mem_filter.1 hMS).2
  have h2 : ∀ t ∈ G.cliqueFinset 3, 2 ≤ #t := fun t ht => by
    rw [(mem_cliqueFinset_iff.1 ht).card_eq]; norm_num
  have hinj : Set.InjOn (fun t : Finset V => t.powersetCard 2)
      ((G.cliqueFinset 3).filter (fun t => t.powersetCard 2 ∈ M) : Set (Finset V)) := by
    intro s hs t ht hst
    exact Nibble.YusterE.powersetCard_two_inj (h2 s (Finset.mem_filter.1 hs).1)
      (h2 t (Finset.mem_filter.1 ht).1) hst
  refine ⟨(G.cliqueFinset 3).filter (fun t => t.powersetCard 2 ∈ M), ⟨Finset.filter_subset _ _,
    fun s hs t ht hst => ?_⟩, ?_⟩
  · by_contra hlt
    obtain ⟨u, hu, hu2⟩ := Finset.exists_subset_card_eq (show 2 ≤ #(s ∩ t) by omega)
    have hne : s.powersetCard 2 ≠ t.powersetCard 2 := fun h => hst (hinj hs ht h)
    have hdis := hM.disjoint _ (Finset.mem_filter.1 hs).2 _ (Finset.mem_filter.1 ht).2 hne
    have hus : u ∈ s.powersetCard 2 :=
      Finset.mem_powersetCard.2 ⟨hu.trans Finset.inter_subset_left, hu2⟩
    have hut : u ∈ t.powersetCard 2 :=
      Finset.mem_powersetCard.2 ⟨hu.trans Finset.inter_subset_right, hu2⟩
    exact Finset.disjoint_left.1 hdis hus hut
  · rw [hnu, hMc, ← Finset.card_image_of_injOn hinj]
    congr 1
    ext T
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨t, ⟨_, htM⟩, rfl⟩
      exact htM
    · intro hT
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 (hM.subset hT)
      exact ⟨t, ⟨ht, hT⟩, rfl⟩

/-- **The fractional cover–integral packing gap for triangles is `o(n²)`.** For every `ε > 0`,
every large enough finite graph has an edge-disjoint triangle family `P` and a fractional triangle
cover of total weight at most `|P| + ε n²`. -/
theorem triangle_cover_packing_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        ∃ P : Finset (Finset V), ∃ y : Sym2 V → ℝ, IsTrianglePacking G P ∧
          IsFracTriangleCover G y ∧
            ∑ e ∈ G.edgeFinset, y e ≤ (#P : ℝ) + ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ :=
    LeanPool.AsymptoticTrianglePacking.triangleCoverPackingGap (ε / 2) (by positivity)
  refine ⟨max n₀ 1, fun V _ _ G _ hn => ?_⟩
  have hgap := hn₀ V G (le_of_max_le_left hn)
  set c : ℝ := (Fintype.card V : ℝ) ^ 2
  have hc : 0 < c := by
    have : (1 : ℝ) ≤ Fintype.card V := by exact_mod_cast le_of_max_le_right hn
    positivity
  obtain ⟨P, hP, hcard⟩ := exists_packing_card_eq_nu3 G
  set S := {x : ℝ | ∃ y : Sym2 V → ℝ, Nibble.AX1.IsFracCover G y ∧
    x = ∑ e ∈ G.edgeFinset, y e}
  have hτ : Nibble.AX1.tau3Star G = sInf S := rfl
  have hne : S.Nonempty := by
    refine ⟨_, fun _ => 1, ⟨fun _ => zero_le_one, fun t ht => ?_⟩, rfl⟩
    rw [mem_cliqueFinset_iff] at ht
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 (by rw [ht.card_eq]; norm_num)
    have hmem : s(a, b) ∈ Nibble.AX1.edgesIn G t := by
      simp only [Nibble.AX1.edgesIn, Finset.mem_filter, mem_edgeFinset, mem_edgeSet]
      refine ⟨ht.isClique ha hb hab, fun v hv => ?_⟩
      rcases Sym2.mem_iff.1 hv with rfl | rfl <;> assumption
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast Finset.card_pos.2 ⟨_, hmem⟩
  have hlt : sInf S < sInf S + ε / 2 * c := lt_add_of_pos_right _ (by positivity)
  obtain ⟨x, ⟨y, hy, rfl⟩, hx⟩ := exists_lt_of_csInf_lt hne hlt
  refine ⟨P, y, hP, hy, ?_⟩
  rw [hcard]
  have : ε * c = 2 * (ε / 2 * c) := by ring
  linarith

/-- **The fractional–integral triangle-packing gap is `o(n²)`.** For every `ε > 0`, every large
enough finite graph has an edge-disjoint triangle family `P` with `ν*(G) ≤ |P| + ε n²`. -/
theorem fractional_triangle_packing_gap (ε : ℝ) (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      n₀ ≤ Fintype.card V →
        ∃ P : Finset (Finset V), IsTrianglePacking G P ∧
          ∀ w : Finset V → ℝ, IsFracTrianglePacking G w →
            ∑ t ∈ G.cliqueFinset 3, w t ≤ (#P : ℝ) + ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨n₀, hn₀⟩ := triangle_cover_packing_gap ε hε
  refine ⟨n₀, fun V _ _ G _ hn => ?_⟩
  obtain ⟨P, y, hP, hy, hval⟩ := hn₀ V G hn
  exact ⟨P, hP, fun w hw => (sum_le_of_packing_cover G hw hy).trans hval⟩

end AsymptoticTrianglePacking
