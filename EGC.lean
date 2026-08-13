/-
A Lean 4 / Mathlib formalization of:

  Andrew Bisch, "Two Thirds of the Vertices of a Minimal Counterexample to the
  Erdős–Gyárfás Conjecture are Cubic" (note, July 2026).

We formalize:
  * the notion of a counterexample to the Erdős–Gyárfás conjecture
    (finite nonempty graph, minimum degree ≥ 3, no cycle of length 2^k);
  * a *minimal* counterexample (lexicographically minimal (order, size) among
    all counterexamples on all finite vertex types in the same universe);
  * Lemma 1 in the two instantiations the paper uses (single-edge deletion and
    deletion of a set of at most two vertices);
  * Lemma 2 (i): vertices of degree ≥ 4 form an independent set   [Markström/Carr]
  * Lemma 2 (ii): every vertex has a neighbor of degree exactly 3 [Carr]
  * Theorem 3: 2·|V(G)| ≤ 3·|V₃|, i.e. at least two thirds of the vertices of a
    minimal counterexample are cubic  (the paper's main bound), and
  * Proposition 4: two adjacent cubic vertices whose four remaining neighbors
    all have degree ≥ 4 have a unique common neighbor, of degree exactly 4.
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Tactic

open Finset SimpleGraph

universe u

namespace EGC

/-! ### Power-of-two cycles -/

/-- A graph has a power-of-two cycle if it contains a cycle whose length is `2 ^ k`
for some `k`.  (In a simple graph any cycle has length ≥ 3, so `k ≥ 2` is automatic.) -/
def HasPow2Cycle {W : Type*} (H : SimpleGraph W) : Prop :=
  ∃ (w : W) (c : H.Walk w w), c.IsCycle ∧ ∃ k : ℕ, c.length = 2 ^ k

/-- Power-of-two cycles transfer along injective graph homomorphisms. -/
theorem HasPow2Cycle.map {W W' : Type*} {H : SimpleGraph W} {K : SimpleGraph W'}
    (f : H →g K) (hf : Function.Injective f) : HasPow2Cycle H → HasPow2Cycle K := by
  rintro ⟨w, c, hc, k, hk⟩
  refine ⟨f w, c.map f, (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc, k, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  exact hk

/-- Power-of-two cycles transfer along subgraph inclusions (same vertex set). -/
theorem HasPow2Cycle.mono {W : Type*} {H K : SimpleGraph W} (hle : H ≤ K) :
    HasPow2Cycle H → HasPow2Cycle K :=
  HasPow2Cycle.map (.ofLE hle) (fun _ _ h => h)

/-- Power-of-two cycles in an induced subgraph give power-of-two cycles in the graph. -/
theorem HasPow2Cycle.of_induce {W : Type*} {H : SimpleGraph W} {s : Set W} :
    HasPow2Cycle (H.induce s) → HasPow2Cycle H := by
  rintro ⟨w, c, hc, k, hk⟩
  let f : H.induce s →g H := ⟨Subtype.val, fun {a b} hab => hab⟩
  have hf : Function.Injective f := Subtype.val_injective
  exact ⟨↑w, c.map f, (SimpleGraph.Walk.isCycle_map_iff_of_injective hf).mpr hc, k, by
    rwa [SimpleGraph.Walk.length_map]⟩

/-! ### Counterexamples and minimal counterexamples -/

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A counterexample to the Erdős–Gyárfás conjecture: a finite nonempty graph with
minimum degree at least 3 and no cycle of power-of-two length. -/
structure IsCounterexample : Prop where
  nonempty : Nonempty V
  degree_ge : ∀ v : V, 3 ≤ G.degree v
  no_pow2 : ¬ HasPow2Cycle G

/-- A *minimal* counterexample: a counterexample which is lexicographically minimal in
(order, size) among all counterexamples (on any finite vertex type in the same universe).
This matches the definition in the paper (and in Carr's note). -/
structure IsMinCex : Prop extends IsCounterexample G where
  minimal : ∀ (W : Type u) [Fintype W] (H : SimpleGraph W) [DecidableRel H.Adj],
    IsCounterexample H →
    Fintype.card V < Fintype.card W ∨
      (Fintype.card V = Fintype.card W ∧ G.edgeSet.ncard ≤ H.edgeSet.ncard)

variable {G}

namespace IsMinCex

/-- A minimal counterexample has at least four vertices. -/
theorem four_le_card (hG : IsMinCex G) : 4 ≤ Fintype.card V := by
  obtain ⟨v⟩ := hG.nonempty
  have h1 := hG.degree_ge v
  have h2 := G.degree_lt_card_verts v
  omega

/-- Minimality, size version: a proper subgraph of a minimal counterexample on the same
vertex set with minimum degree ≥ 3 contains a power-of-two cycle.
(This is the way Lemma 1 is used for single-edge deletions.) -/
theorem min_size (hG : IsMinCex G) (H : SimpleGraph V) [DecidableRel H.Adj]
    (hle : H ≤ G) (hne : H ≠ G) (hdeg : ∀ v, 3 ≤ H.degree v) : HasPow2Cycle H := by
  by_contra hno
  have hcex : IsCounterexample H := ⟨hG.nonempty, hdeg, hno⟩
  rcases hG.minimal V H hcex with h | ⟨-, h⟩
  · exact lt_irrefl _ h
  · have hsub : H.edgeSet ⊆ G.edgeSet := edgeSet_mono hle
    have hfin : G.edgeSet.Finite := G.edgeSet.toFinite
    have : G.edgeSet = H.edgeSet := (Set.eq_of_subset_of_ncard_le hsub h hfin).symm
    exact hne (edgeSet_injective this.symm)

/-- Minimality, order version: a graph on strictly fewer vertices with minimum degree ≥ 3
contains a power-of-two cycle. -/
theorem min_order (hG : IsMinCex G) (W : Type u) [Fintype W] (H : SimpleGraph W)
    [DecidableRel H.Adj] (hW : Nonempty W) (hcard : Fintype.card W < Fintype.card V)
    (hdeg : ∀ w, 3 ≤ H.degree w) : HasPow2Cycle H := by
  by_contra hno
  rcases hG.minimal W H ⟨hW, hdeg, hno⟩ with h | ⟨h, -⟩ <;> omega

end IsMinCex

/-! ### Deleting a small set of vertices (the paper's Lemma 1, vertex-deletion form) -/

section Induce

variable [DecidableEq V]

/-- Adjacency in an induced subgraph is decidable. -/
instance instDecidableRelInduceAdj (s : Set V) :
    DecidableRel (G.induce s).Adj := fun a b =>
  decidable_of_iff (G.Adj ↑a ↑b) Iff.rfl

/-- The degree of a vertex of `G.induce {x | x ∉ T}` counts the neighbors outside `T`. -/
theorem degree_induce_compl (T : Finset V) (w : ↥({x : V | x ∉ T} : Set V)) :
    (G.induce ({x : V | x ∉ T} : Set V)).degree w = ((G.neighborFinset ↑w) \ T).card := by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun a _ => (↑a : V)) ?_ ?_ ?_
  · rintro ⟨a, ha⟩ hmem
    rw [mem_neighborFinset] at hmem
    rw [Finset.mem_sdiff, mem_neighborFinset]
    exact ⟨hmem, ha⟩
  · exact fun a _ b _ h => Subtype.ext h
  · rintro y hy
    rw [Finset.mem_sdiff, mem_neighborFinset] at hy
    exact ⟨⟨y, hy.2⟩, by rw [mem_neighborFinset]; exact hy.1, rfl⟩

/-- **Lemma 1, vertex-deletion form.**  Deleting a nonempty set `T` of at most two vertices
from a minimal counterexample leaves some vertex `x ∉ T` with at most two neighbors
outside `T`. -/
theorem IsMinCex.exists_low_degree_delete (hG : IsMinCex G) (T : Finset V)
    (hT : T.Nonempty) (hTcard : T.card ≤ 2) :
    ∃ x, x ∉ T ∧ ((G.neighborFinset x) \ T).card ≤ 2 := by
  by_contra hcon
  simp only [not_exists, not_and, not_le] at hcon
  -- the vertex set of the deleted graph is nonempty …
  have hcard4 := hG.four_le_card
  have huniv : (Finset.univ \ T).card = Fintype.card V - T.card := by
    rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
  have hex : ∃ x : V, x ∉ T := by
    have : 0 < (Finset.univ \ T).card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp this
    exact ⟨x, (Finset.mem_sdiff.mp hx).2⟩
  obtain ⟨x₀, hx₀⟩ := hex
  have hne : Nonempty ↥({x : V | x ∉ T} : Set V) := ⟨⟨x₀, hx₀⟩⟩
  -- … and strictly smaller than `V`
  obtain ⟨t₀, ht₀⟩ := hT
  have hlt : Fintype.card ↥({x : V | x ∉ T} : Set V) < Fintype.card V := by
    have hts : ¬ t₀ ∈ ({x : V | x ∉ T} : Set V) := by
      simp only [Set.mem_setOf_eq, not_not]
      exact ht₀
    exact Fintype.card_subtype_lt (p := fun x => x ∈ ({x : V | x ∉ T} : Set V)) hts
  -- all degrees of the deleted graph are ≥ 3, by assumption
  have hdeg : ∀ w : ↥({x : V | x ∉ T} : Set V),
      3 ≤ (G.induce ({x : V | x ∉ T} : Set V)).degree w := by
    rintro w
    rw [degree_induce_compl]
    have := hcon _ w.2
    omega
  -- so minimality produces a power-of-two cycle in it, hence in `G`: contradiction
  exact hG.no_pow2 <| HasPow2Cycle.of_induce <|
    hG.min_order _ (G.induce ({x : V | x ∉ T} : Set V)) hne hlt hdeg

end Induce

/-! ### Lemma 2 -/

section Lemma2

variable [DecidableEq V]

/-- **Lemma 2 (ii)** (Carr).  Every vertex of a minimal counterexample is adjacent to a
vertex of degree exactly 3. -/
theorem IsMinCex.exists_cubic_neighbor (hG : IsMinCex G) (v : V) :
    ∃ x, G.Adj v x ∧ G.degree x = 3 := by
  obtain ⟨x, hxT, hx⟩ :=
    hG.exists_low_degree_delete (T := {v}) (Finset.singleton_nonempty v) (by simp)
  have hxv : x ≠ v := by simpa using hxT
  have hdx := hG.degree_ge x
  have hsd : G.neighborFinset x \ {v} = (G.neighborFinset x).erase v := by
    ext y; simp [Finset.mem_sdiff, Finset.mem_erase, and_comm]
  by_cases hadj : G.Adj x v
  · refine ⟨x, hadj.symm, ?_⟩
    have hv_mem : v ∈ G.neighborFinset x := (G.mem_neighborFinset x v).mpr hadj
    rw [hsd, Finset.card_erase_of_mem hv_mem, card_neighborFinset_eq_degree] at hx
    omega
  · exfalso
    have hv_nmem : v ∉ G.neighborFinset x := by
      rw [mem_neighborFinset]; exact hadj
    rw [hsd, Finset.erase_eq_of_notMem hv_nmem, card_neighborFinset_eq_degree] at hx
    omega

/-- **Lemma 2 (i)** (Markström, Carr).  In a minimal counterexample, no two vertices of
degree at least 4 are adjacent, i.e. `V≥4` is an independent set. -/
theorem IsMinCex.not_adj_of_four_le_degree (hG : IsMinCex G) {u w : V}
    (hu : 4 ≤ G.degree u) (hw : 4 ≤ G.degree w) : ¬ G.Adj u w := by
  intro hadj
  have huw : u ≠ w := hadj.ne
  set H : SimpleGraph V := G.deleteEdges {s(u, w)} with hH
  haveI : DecidableRel H.Adj := fun a b =>
    decidable_of_iff (G.Adj a b ∧ ¬ s(a, b) = s(u, w)) (by
      rw [hH, deleteEdges_adj, Set.mem_singleton_iff])
  -- neighbor sets of the edge-deleted graph
  have hnbu : H.neighborFinset u = (G.neighborFinset u).erase w := by
    ext y
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨hGy, hne⟩
      refine ⟨fun hyw => hne (Or.inl ⟨rfl, hyw⟩), hGy⟩
    · rintro ⟨hyw, hGy⟩
      refine ⟨hGy, ?_⟩
      rintro (⟨-, h⟩ | ⟨h, -⟩)
      · exact hyw h
      · exact huw h
  have hnbw : H.neighborFinset w = (G.neighborFinset w).erase u := by
    ext y
    rw [mem_neighborFinset, Finset.mem_erase, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨hGy, hne⟩
      refine ⟨fun hyu => hne (Or.inr ⟨rfl, hyu⟩), hGy⟩
    · rintro ⟨hyu, hGy⟩
      refine ⟨hGy, ?_⟩
      rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact huw h.symm
      · exact hyu h
  have hnbo : ∀ x, x ≠ u → x ≠ w → H.neighborFinset x = G.neighborFinset x := by
    intro x hxu hxw
    ext y
    rw [mem_neighborFinset, mem_neighborFinset, hH, deleteEdges_adj,
      Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · exact fun h => h.1
    · intro h
      refine ⟨h, ?_⟩
      rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact hxu h1
      · exact hxw h1
  -- the deleted graph still has minimum degree ≥ 3
  have hdeg : ∀ v, 3 ≤ H.degree v := by
    intro x
    rcases eq_or_ne x u with rfl | hxu
    · rw [← card_neighborFinset_eq_degree, hnbu,
        Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj),
        card_neighborFinset_eq_degree]
      omega
    rcases eq_or_ne x w with rfl | hxw
    · rw [← card_neighborFinset_eq_degree, hnbw,
        Finset.card_erase_of_mem ((G.mem_neighborFinset _ _).mpr hadj.symm),
        card_neighborFinset_eq_degree]
      omega
    · rw [← card_neighborFinset_eq_degree, hnbo x hxu hxw,
        card_neighborFinset_eq_degree]
      exact hG.degree_ge x
  -- it is a proper subgraph
  have hne : H ≠ G := by
    intro h
    have : H.Adj u w := h ▸ hadj
    rw [hH, deleteEdges_adj] at this
    exact this.2 (Set.mem_singleton _)
  -- contradiction with minimality
  exact hG.no_pow2 <| HasPow2Cycle.mono (deleteEdges_le _) <|
    hG.min_size H (deleteEdges_le _) hne hdeg

end Lemma2

/-! ### Theorem 3: the 2/3 bound -/

/-- **The counting step of Theorem 3**, isolated: if a finite graph has minimum degree ≥ 3,
its vertices of degree ≥ 4 form an independent set, and every cubic vertex has a cubic
neighbor, then at least two thirds of its vertices are cubic:  `2·|V| ≤ 3·|V₃|`. -/
theorem two_thirds_count
    (hdeg : ∀ v, 3 ≤ G.degree v)
    (hindep : ∀ u w, 4 ≤ G.degree u → 4 ≤ G.degree w → ¬ G.Adj u w)
    (hdom : ∀ v, G.degree v = 3 → ∃ x, G.Adj v x ∧ G.degree x = 3) :
    2 * Fintype.card V ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card := by
  classical
  -- `V₃` and `V₄` partition the vertex set
  have hpart : (Finset.univ.filter fun v => G.degree v = 3).card
      + (Finset.univ.filter fun v => 4 ≤ G.degree v).card = Fintype.card V := by
    have heq : (Finset.univ.filter fun v => ¬ G.degree v = 3)
        = (Finset.univ.filter fun v => 4 ≤ G.degree v) := by
      apply Finset.filter_congr
      intro v _
      have := hdeg v
      omega
    have h0 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset V))
      (fun v => G.degree v = 3)
    rw [heq, Finset.card_univ] at h0
    exact h0
  set V3 : Finset V := Finset.univ.filter (fun v => G.degree v = 3) with hV3
  set V4 : Finset V := Finset.univ.filter (fun v => 4 ≤ G.degree v) with hV4
  -- every neighbor of a vertex of `V₄` is cubic
  have hnb4 : ∀ u ∈ V4, ∀ x, G.Adj u x → G.degree x = 3 := by
    intro u hu x hx
    have hu4 : 4 ≤ G.degree u := (Finset.mem_filter.mp hu).2
    have h3 := hdeg x
    rcases Nat.lt_or_ge (G.degree x) 4 with h | h
    · omega
    · exact absurd hx (hindep u x hu4 h)
  -- hence the degree sum over `V₄` counts edges into `V₃` …
  have hleft : ∀ u ∈ V4, G.degree u = (V3.filter (fun v => G.Adj u v)).card := by
    intro u hu
    rw [← card_neighborFinset_eq_degree]
    congr 1
    ext x
    rw [mem_neighborFinset, Finset.mem_filter, hV3, Finset.mem_filter]
    constructor
    · intro h; exact ⟨⟨Finset.mem_univ x, hnb4 u hu x h⟩, h⟩
    · exact fun h => h.2
  -- … and the double count can be flipped
  have hswap : ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card
      = ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  -- each cubic vertex sends at most two edges to `V₄`
  have hup : ∀ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card ≤ 2 := by
    intro v hv
    have hv3 : G.degree v = 3 := (Finset.mem_filter.mp hv).2
    obtain ⟨x, hvx, hx3⟩ := hdom v hv3
    have hsub : V4.filter (fun u => G.Adj u v) ⊆ (G.neighborFinset v).erase x := by
      intro y hy
      rw [Finset.mem_filter, hV4, Finset.mem_filter] at hy
      rw [Finset.mem_erase, mem_neighborFinset]
      refine ⟨?_, hy.2.symm⟩
      rintro rfl
      omega
    calc (V4.filter (fun u => G.Adj u v)).card
        ≤ ((G.neighborFinset v).erase x).card := Finset.card_le_card hsub
      _ = G.degree v - 1 := by
          rw [Finset.card_erase_of_mem ((G.mem_neighborFinset v x).mpr hvx),
            card_neighborFinset_eq_degree]
      _ ≤ 2 := by omega
  -- put the counts together
  have hlow : 4 * V4.card ≤ ∑ u ∈ V4, G.degree u := by
    have := Finset.card_nsmul_le_sum V4 (fun u => G.degree u) 4
      (fun u hu => (Finset.mem_filter.mp hu).2)
    simpa [mul_comm] using this
  have hhigh : ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card ≤ 2 * V3.card := by
    have := Finset.sum_le_card_nsmul V3 (fun v => (V4.filter (fun u => G.Adj u v)).card) 2 hup
    simpa [mul_comm] using this
  have hsum : ∑ u ∈ V4, G.degree u = ∑ u ∈ V4, (V3.filter (fun v => G.Adj u v)).card :=
    Finset.sum_congr rfl hleft
  -- 4|V₄| ≤ 2|V₃|, and |V₃| + |V₄| = |V|, so 2|V| ≤ 3|V₃|
  have : 4 * V4.card ≤ 2 * V3.card := by
    calc 4 * V4.card ≤ ∑ u ∈ V4, G.degree u := hlow
      _ = ∑ v ∈ V3, (V4.filter (fun u => G.Adj u v)).card := by rw [hsum, hswap]
      _ ≤ 2 * V3.card := hhigh
  omega

/-- **Theorem 3.**  At least two thirds of the vertices of a minimal counterexample to the
Erdős–Gyárfás conjecture have degree exactly 3:  `2·|V(G)| ≤ 3·|V₃|`. -/
theorem IsMinCex.two_thirds [DecidableEq V] (hG : IsMinCex G) :
    2 * Fintype.card V ≤ 3 * (Finset.univ.filter fun v => G.degree v = 3).card :=
  two_thirds_count hG.degree_ge (fun _ _ hu hw => hG.not_adj_of_four_le_degree hu hw)
    (fun v _ => hG.exists_cubic_neighbor v)

/-- Theorem 3, restated over `ℚ`:  `|V₃| ≥ (2/3)·|V(G)|`. -/
theorem IsMinCex.two_thirds_rat [DecidableEq V] (hG : IsMinCex G) :
    (2 / 3 : ℚ) * Fintype.card V
      ≤ ((Finset.univ.filter fun v => G.degree v = 3).card : ℚ) := by
  have h := hG.two_thirds
  have h' : (2 * Fintype.card V : ℚ)
      ≤ 3 * ((Finset.univ.filter fun v => G.degree v = 3).card : ℚ) := by
    exact_mod_cast h
  linarith

/-! ### Proposition 4 -/

/-- A minimal counterexample contains no 4-cycle (since `4 = 2²`): given the four sides of
a quadrilateral with distinct opposite corners, we get a contradiction. -/
theorem IsMinCex.no_c4 (hG : IsMinCex G) {a b c d : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hda : G.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  apply hG.no_pow2
  have h1 : a ≠ b := hab.ne
  have h2 : b ≠ c := hbc.ne
  have h3 : c ≠ d := hcd.ne
  have h4 : d ≠ a := hda.ne
  -- the six pairwise inequalities between the four edges of the quadrilateral
  have d1 : s(a, b) ≠ s(b, c) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact h1 h
    · exact hac h
  have d2 : s(a, b) ≠ s(c, d) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact hac h
    · exact h4 h.symm
  have d3 : s(a, b) ≠ s(d, a) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨-, h⟩)
    · exact h4 h.symm
    · exact hbd h
  have d4 : s(b, c) ≠ s(c, d) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact h2 h
    · exact hbd h
  have d5 : s(b, c) ≠ s(d, a) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact hbd h
    · exact h1 h.symm
  have d6 : s(c, d) ≠ s(d, a) := by
    intro hh
    rw [Sym2.eq_iff] at hh
    rcases hh with (⟨h, -⟩ | ⟨h, -⟩)
    · exact h3 h
    · exact hac h.symm
  refine ⟨a, .cons hab (.cons hbc (.cons hcd (.cons hda .nil))), ?_, 2, by simp⟩
  rw [SimpleGraph.Walk.isCycle_def]
  refine ⟨?_, by simp, ?_⟩
  · rw [SimpleGraph.Walk.isTrail_def]
    simp [d1, d2, d3, d4, d5, d6]
  · simp [h2, h3, h4, hbd, h1.symm, hac.symm]

/-- **Proposition 4.**  Let `v v'` be adjacent cubic vertices of a minimal counterexample
all of whose remaining neighbors have degree at least 4.  Then `v` and `v'` have exactly
one common neighbor `u`, and `u` has degree exactly 4 (so `v, v', u` form a triangle whose
apex has degree 4). -/
theorem IsMinCex.common_neighbor [DecidableEq V] (hG : IsMinCex G) {v v' : V}
    (hadj : G.Adj v v')
    -- (the cubic hypotheses of the paper's statement are recorded for faithfulness,
    -- but the argument below does not need them)
    (_hv : G.degree v = 3) (_hv' : G.degree v' = 3)
    (hnb : ∀ x, G.Adj v x → x ≠ v' → 4 ≤ G.degree x)
    (hnb' : ∀ x, G.Adj v' x → x ≠ v → 4 ≤ G.degree x) :
    ∃ u, G.Adj v u ∧ G.Adj v' u ∧ G.degree u = 4 ∧
      ∀ y, G.Adj v y → G.Adj v' y → y = u := by
  have hvv' : v ≠ v' := hadj.ne
  -- delete the pair {v, v'}
  obtain ⟨x, hxT, hx⟩ := hG.exists_low_degree_delete (T := {v, v'})
    (Finset.insert_nonempty v {v'}) ((Finset.card_insert_le v {v'}).trans (by simp))
  have hxv : x ≠ v := by simp at hxT; tauto
  have hxv' : x ≠ v' := by simp at hxT; tauto
  have hdx := hG.degree_ge x
  -- rewrite the deleted neighborhood as a double `erase`
  have hsd : G.neighborFinset x \ {v, v'} = ((G.neighborFinset x).erase v').erase v := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
      Finset.mem_erase]
    tauto
  rw [hsd] at hx
  by_cases hxadjv : G.Adj x v <;> by_cases hxadjv' : G.Adj x v'
  · -- `x` is a common neighbor: it has degree 4 and is unique
    have hv'_mem : v' ∈ G.neighborFinset x := (G.mem_neighborFinset x v').mpr hxadjv'
    have hv_mem : v ∈ (G.neighborFinset x).erase v' :=
      Finset.mem_erase.mpr ⟨hvv', (G.mem_neighborFinset x v).mpr hxadjv⟩
    rw [Finset.card_erase_of_mem hv_mem, Finset.card_erase_of_mem hv'_mem,
      card_neighborFinset_eq_degree] at hx
    have hx4 : 4 ≤ G.degree x := hnb x hxadjv.symm hxv'
    have hxdeg : G.degree x = 4 := by omega
    refine ⟨x, hxadjv.symm, hxadjv'.symm, hxdeg, ?_⟩
    -- uniqueness via the absence of 4-cycles
    intro y hvy hv'y
    by_contra hyx
    exact hG.no_c4 hvy hv'y.symm hxadjv'.symm hxadjv hvv' hyx
  · -- adjacent to `v` only: degree ≥ 4 forces too many surviving neighbors
    exfalso
    have hv'_nmem : v' ∉ G.neighborFinset x := by
      rw [mem_neighborFinset]; exact hxadjv'
    rw [Finset.erase_eq_of_notMem hv'_nmem, Finset.card_erase_of_mem
      ((G.mem_neighborFinset x v).mpr hxadjv), card_neighborFinset_eq_degree] at hx
    have := hnb x hxadjv.symm hxv'
    omega
  · -- adjacent to `v'` only: same
    exfalso
    have hv'_mem : v' ∈ G.neighborFinset x := (G.mem_neighborFinset x v').mpr hxadjv'
    have hv_nmem : v ∉ (G.neighborFinset x).erase v' := by
      rw [Finset.mem_erase, mem_neighborFinset]
      rintro ⟨-, h⟩; exact hxadjv h
    rw [Finset.erase_eq_of_notMem hv_nmem, Finset.card_erase_of_mem hv'_mem,
      card_neighborFinset_eq_degree] at hx
    have := hnb' x hxadjv'.symm hxv
    omega
  · -- adjacent to neither: all three neighbors survive
    exfalso
    have hv'_nmem : v' ∉ G.neighborFinset x := by
      rw [mem_neighborFinset]; exact hxadjv'
    have hv_nmem : v ∉ (G.neighborFinset x).erase v' := by
      rw [Finset.mem_erase, mem_neighborFinset]
      rintro ⟨-, h⟩; exact hxadjv h
    rw [Finset.erase_eq_of_notMem hv_nmem, Finset.erase_eq_of_notMem hv'_nmem,
      card_neighborFinset_eq_degree] at hx
    omega

end EGC

/-! ### Axiom audit: the proofs use only the standard axioms -/

#print axioms EGC.IsMinCex.two_thirds
#print axioms EGC.IsMinCex.two_thirds_rat
#print axioms EGC.IsMinCex.exists_cubic_neighbor
#print axioms EGC.IsMinCex.not_adj_of_four_le_degree
#print axioms EGC.IsMinCex.common_neighbor
