import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open Finset SimpleGraph

/- Originally, the scope of the project was to just formulate the first theorem you
see but it turned out much shorter than I expected so I ended up adding some more lemmas
that are either closely related or directly build off of the first one to make the
project a little bit more comprehensive. -/

variable {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V)

def IsBipartition (V₁ V₂ : Finset V) : Prop :=
  Disjoint V₁ V₂ ∧
  V₁ ∪ V₂ = Finset.univ ∧
  ∀ ⦃u v : V⦄, G.Adj u v → (u ∈ V₁ ∧ v ∈ V₂) ∨ (u ∈ V₂ ∧ v ∈ V₁)

/- Lemma 1: Let G be a finite bipartite graph with bipartition (V₁, V₂).
 If G has a perfect matching, then |V₁| = |V₂|. -/
theorem bipartite_perfect_matching_card_eq
    (V₁ V₂ : Finset V)
    (h_bip : IsBipartition G V₁ V₂)
    {M : G.Subgraph}
    (h_perf : M.IsPerfectMatching) :
    V₁.card = V₂.card := by
  obtain ⟨h_disj, _h_cover, h_cross⟩ := h_bip
  rw [Subgraph.isPerfectMatching_iff] at h_perf

  -- Define the bijection mapping the vertex to the partner vertex
  let f : V → V := fun v => (h_perf v).choose
  have hf_adj : ∀ v, M.Adj v (f v) := fun v => ((h_perf v).choose_spec).1
  have hf_uniq : ∀ v w, M.Adj v w → w = f v := fun v w hw => ((h_perf v).choose_spec).2 w hw
  have h_matching : M.IsMatching := by
    intro v _hv_mem
    exact h_perf v
  have not_both : ∀ x : V, x ∈ V₁ → x ∉ V₂ := Finset.disjoint_left.mp h_disj

  -- Use Finset.card_nbij to split the problem into codomain, injectivity, and surjectivity
  refine Finset.card_nbij f ?_ ?_ ?_

  -- 1. Checking the codomain
  · intro v hv
    have hGadj : G.Adj v (f v) := (hf_adj v).adj_sub
    rcases h_cross hGadj with ⟨_, hfv_in_V₂⟩ | ⟨hv_in_V₂, _⟩
    · exact hfv_in_V₂
    · exact absurd hv_in_V₂ (not_both v hv)

  -- 2. Checking injectivity
  · intro v₁ _ v₂ _ heq
    have h1 : M.Adj v₁ (f v₁) := hf_adj v₁
    have h2 : M.Adj v₂ (f v₂) := hf_adj v₂
    rw [← heq] at h2
    exact h_matching.eq_of_adj_right h1 h2

  -- 3. Checking surjectivity
  · intro w hw
    obtain ⟨v, hv_adj_wv, _⟩ := h_perf w
    have hGadj : G.Adj w v := hv_adj_wv.adj_sub
    rcases h_cross hGadj with ⟨hw_in_V₁, _⟩ | ⟨_, hv_in_V₁⟩
    · exact absurd hw (not_both w hw_in_V₁)
    · exact ⟨v, hv_in_V₁, (hf_uniq v w hv_adj_wv.symm).symm⟩

/- Lemma 2: If the two parts have unequal cardinality, no perfect matching can exist. -/
theorem no_perfect_matching_of_card_ne
    (V₁ V₂ : Finset V)
    (h_bip : IsBipartition G V₁ V₂)
    (h_card : V₁.card ≠ V₂.card)
    (M : G.Subgraph) :
    ¬M.IsPerfectMatching := by
  -- First we assume that a perfect matching does exist.
  intro h_perf
  -- Since the a perfect matching must have both set cardinalities equal this directly contradicts the hypothesis.
  exact h_card (bipartite_perfect_matching_card_eq G V₁ V₂ h_bip h_perf)

/- Lemma 3: The number of vertices in a finite bipartite graph that has a perfect matching is even. -/
theorem even_card_of_perfect_matching
    (V₁ V₂ : Finset V)
    (h_bip : IsBipartition G V₁ V₂)
    {M : G.Subgraph}
    (h_perf : M.IsPerfectMatching) :
    Even (Fintype.card V) := by
  -- First we need to get the equality statement from Lemma 1.
  have h_eq : V₁.card = V₂.card :=
    bipartite_perfect_matching_card_eq G V₁ V₂ h_bip h_perf
  obtain ⟨h_disj, h_cover, _⟩ := h_bip
  -- We express the total number of vertices as the sum of the two cardinalities.
  have h_total : V₁.card + V₂.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint h_disj, h_cover]
    simp
  -- Check that 2 * V₁.card is the total vertices.
  exact ⟨V₁.card, by linarith⟩

/- Lemma 4: A bipartite graph with a perfect matching has two sets of vertices that each hold exactly
 half of the vertices in the whole graph. -/
theorem parts_card_eq_half
    (V₁ V₂ : Finset V)
    (h_bip : IsBipartition G V₁ V₂)
    {M : G.Subgraph}
    (h_perf : M.IsPerfectMatching) :
    V₁.card = Fintype.card V / 2 := by
  -- First we need to get the equality statement from Lemma 1.
  have h_eq : V₁.card = V₂.card :=
    bipartite_perfect_matching_card_eq G V₁ V₂ h_bip h_perf
  obtain ⟨h_disj, h_cover, _⟩ := h_bip
  -- -- We express the total number of vertices as the sum of the two cardinalities.
  have h_total : V₁.card + V₂.card = Fintype.card V := by
    rw [← Finset.card_union_of_disjoint h_disj, h_cover]
    simp
  -- omega can infer that V₁ has to be half of the total since V₁.card + V₁.card = total
  omega

/- Lemma 5: If the total number of vertices in a finite bipartite graph is odd, then there is no perfect matching. -/
theorem no_perfect_matching_of_odd_card
    (V₁ V₂ : Finset V)
    (h_bip : IsBipartition G V₁ V₂)
    (h_odd : Odd (Fintype.card V))
    (M : G.Subgraph) :
    ¬M.IsPerfectMatching := by
  -- Assume for contradiction that a perfect matching exists.
  intro h_perf
  -- Lemma 3 already tells us that we need an even number of vertices.
  have h_even := even_card_of_perfect_matching G V₁ V₂ h_bip h_perf
  rcases h_even with ⟨k, hk⟩
  rcases h_odd with ⟨m, hm⟩
  -- The number can't be even and odd at the same time so omega can infer that it is contradictory.
  omega

/- Lemma 6: If one of the sets of vertices contains more than half of the total vertices in the graph, then
 there is no perfect matching. -/
theorem no_perfect_matching_of_part_gt_half
    (V₁ V₂ : Finset V)
    (h_bip : IsBipartition G V₁ V₂)
    (h_gt : V₁.card > Fintype.card V / 2)
    (M : G.Subgraph) :
    ¬M.IsPerfectMatching := by
  -- Assume for contradiction that a perfect matching exists.
  intro h_perf
  -- Lemma 4 already tells us that the cardinality of each set has to be exactly half of the total.
  have h_half := parts_card_eq_half G V₁ V₂ h_bip h_perf
  -- Since the cardinality can't be both equal to and greater than half, omega can infer the contradition.
  omega
