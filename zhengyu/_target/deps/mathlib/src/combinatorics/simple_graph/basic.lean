/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov, Hunter Monroe
-/
import data.rel
import data.set.finite
import data.sym.sym2

/-!
# Simple graphs

This module defines simple graphs on a vertex type `V` as an
irreflexive symmetric relation.

There is a basic API for locally finite graphs and for graphs with
finitely many vertices.

## Main definitions

* `simple_graph` is a structure for symmetric, irreflexive relations

* `neighbor_set` is the `set` of vertices adjacent to a given vertex

* `common_neighbors` is the intersection of the neighbor sets of two given vertices

* `neighbor_finset` is the `finset` of vertices adjacent to a given vertex,
   if `neighbor_set` is finite

* `incidence_set` is the `set` of edges containing a given vertex

* `incidence_finset` is the `finset` of edges containing a given vertex,
   if `incidence_set` is finite

* `homo`, `embedding`, and `iso` for graph homomorphisms, graph embeddings, and
  graph isomorphisms. Note that a graph embedding is a stronger notion than an
  injective graph homomorphism, since its image is an induced subgraph.

* `boolean_algebra` instance: Under the subgraph relation, `simple_graph` forms a `boolean_algebra`.
  In other words, this is the lattice of spanning subgraphs of the complete graph.

## Notations

* `→g`, `↪g`, and `≃g` for graph homomorphisms, graph embeddings, and graph isomorphisms,
  respectively.

## Implementation notes

* A locally finite graph is one with instances `Π v, fintype (G.neighbor_set v)`.

* Given instances `decidable_rel G.adj` and `fintype V`, then the graph
  is locally finite, too.

* Morphisms of graphs are abbreviations for `rel_hom`, `rel_embedding`, and `rel_iso`.
  To make use of pre-existing simp lemmas, definitions involving morphisms are
  abbreviations as well.

## Naming Conventions

* If the vertex type of a graph is finite, we refer to its cardinality as `card_verts`.

## Todo

* Upgrade `simple_graph.boolean_algebra` to a `complete_boolean_algebra`.

* This is the simplest notion of an unoriented graph.  This should
  eventually fit into a more complete combinatorics hierarchy which
  includes multigraphs and directed graphs.  We begin with simple graphs
  in order to start learning what the combinatorics hierarchy should
  look like.
-/
open finset
universes u v w

/--
A simple graph is an irreflexive symmetric relation `adj` on a vertex type `V`.
The relation describes which pairs of vertices are adjacent.
There is exactly one edge for every pair of adjacent vertices;
see `simple_graph.edge_set` for the corresponding edge set.
-/
@[ext]
structure simple_graph (V : Type u) :=
(adj : V → V → Prop)
(symm : symmetric adj . obviously)
(loopless : irreflexive adj . obviously)

/--
Construct the simple graph induced by the given relation. It
symmetrizes the relation and makes it irreflexive.
-/
def simple_graph.from_rel {V : Type u} (r : V → V → Prop) : simple_graph V :=
{ adj := λ a b, (a ≠ b) ∧ (r a b ∨ r b a),
  symm := λ a b ⟨hn, hr⟩, ⟨hn.symm, hr.symm⟩,
  loopless := λ a ⟨hn, _⟩, hn rfl }

noncomputable instance {V : Type u} [fintype V] : fintype (simple_graph V) :=
by { classical, exact fintype.of_injective simple_graph.adj simple_graph.ext }

@[simp]
lemma simple_graph.from_rel_adj {V : Type u} (r : V → V → Prop) (v w : V) :
  (simple_graph.from_rel r).adj v w ↔ v ≠ w ∧ (r v w ∨ r w v) :=
iff.rfl

/-- The complete graph on a type `V` is the simple graph with all pairs of distinct vertices
adjacent. In `mathlib`, this is usually referred to as `⊤`. -/
def complete_graph (V : Type u) : simple_graph V := { adj := ne }

/-- The graph with no edges on a given vertex type `V`. `mathlib` prefers the notation `⊥`. -/
def empty_graph (V : Type u) : simple_graph V := { adj := λ i j, false }

/--
Two vertices are adjacent in the complete bipartite graph on two vertex types
if and only if they are not from the same side.
Bipartite graphs in general may be regarded as being subgraphs of one of these.

TODO also introduce complete multi-partite graphs, where the vertex type is a sigma type of an
indexed family of vertex types
-/
@[simps]
def complete_bipartite_graph (V W : Type*) : simple_graph (V ⊕ W) :=
{ adj := λ v w, (v.is_left ∧ w.is_right) ∨ (v.is_right ∧ w.is_left),
  symm := begin
    intros v w,
    cases v; cases w; simp,
  end,
  loopless := begin
    intro v,
    cases v; simp,
  end }

namespace simple_graph

variables {V : Type u} {W : Type v} {X : Type w} (G : simple_graph V) (G' : simple_graph W)
  {a b c u v w : V} {e : sym2 V}

@[simp] lemma irrefl {v : V} : ¬G.adj v v := G.loopless v

lemma adj_comm (u v : V) : G.adj u v ↔ G.adj v u := ⟨λ x, G.symm x, λ x, G.symm x⟩

@[symm] lemma adj_symm (h : G.adj u v) : G.adj v u := G.symm h

lemma ne_of_adj (h : G.adj a b) : a ≠ b := by { rintro rfl, exact G.irrefl h }

protected lemma adj.ne {G : simple_graph V} {a b : V} (h : G.adj a b) : a ≠ b := G.ne_of_adj h

protected lemma adj.ne' {G : simple_graph V} {a b : V} (h : G.adj a b) : b ≠ a := h.ne.symm

lemma ne_of_adj_of_not_adj {v w x : V} (h : G.adj v x) (hn : ¬ G.adj w x) : v ≠ w :=
λ h', hn (h' ▸ h)

section order

/-- The relation that one `simple_graph` is a subgraph of another.
Note that this should be spelled `≤`. -/
def is_subgraph (x y : simple_graph V) : Prop := ∀ ⦃v w : V⦄, x.adj v w → y.adj v w

instance : has_le (simple_graph V) := ⟨is_subgraph⟩

@[simp] lemma is_subgraph_eq_le : (is_subgraph : simple_graph V → simple_graph V → Prop) = (≤) :=
rfl

/-- The supremum of two graphs `x ⊔ y` has edges where either `x` or `y` have edges. -/
instance : has_sup (simple_graph V) := ⟨λ x y,
  { adj := x.adj ⊔ y.adj,
    symm := λ v w h, by rwa [pi.sup_apply, pi.sup_apply, x.adj_comm, y.adj_comm] }⟩

@[simp] lemma sup_adj (x y : simple_graph V) (v w : V) : (x ⊔ y).adj v w ↔ x.adj v w ∨ y.adj v w :=
iff.rfl

/-- The infimum of two graphs `x ⊓ y` has edges where both `x` and `y` have edges. -/
instance : has_inf (simple_graph V) := ⟨λ x y,
  { adj := x.adj ⊓ y.adj,
    symm := λ v w h, by rwa [pi.inf_apply, pi.inf_apply, x.adj_comm, y.adj_comm] }⟩

@[simp] lemma inf_adj (x y : simple_graph V) (v w : V) : (x ⊓ y).adj v w ↔ x.adj v w ∧ y.adj v w :=
iff.rfl

/--
We define `Gᶜ` to be the `simple_graph V` such that no two adjacent vertices in `G`
are adjacent in the complement, and every nonadjacent pair of vertices is adjacent
(still ensuring that vertices are not adjacent to themselves).
-/
instance : has_compl (simple_graph V) := ⟨λ G,
  { adj := λ v w, v ≠ w ∧ ¬G.adj v w,
    symm := λ v w ⟨hne, _⟩, ⟨hne.symm, by rwa adj_comm⟩,
    loopless := λ v ⟨hne, _⟩, (hne rfl).elim }⟩

@[simp] lemma compl_adj (G : simple_graph V) (v w : V) : Gᶜ.adj v w ↔ v ≠ w ∧ ¬G.adj v w := iff.rfl

/-- The difference of two graphs `x \ y` has the edges of `x` with the edges of `y` removed. -/
instance : has_sdiff (simple_graph V) := ⟨λ x y,
  { adj := x.adj \ y.adj,
    symm := λ v w h, by change x.adj w v ∧ ¬ y.adj w v; rwa [x.adj_comm, y.adj_comm] }⟩

@[simp] lemma sdiff_adj (x y : simple_graph V) (v w : V) :
  (x \ y).adj v w ↔ (x.adj v w ∧ ¬ y.adj v w) := iff.rfl

instance : boolean_algebra (simple_graph V) :=
{ le := (≤),
  sup := (⊔),
  inf := (⊓),
  compl := has_compl.compl,
  sdiff := (\),
  top := complete_graph V,
  bot := empty_graph V,
  le_top := λ x v w h, x.ne_of_adj h,
  bot_le := λ x v w h, h.elim,
  sup_le := λ x y z hxy hyz v w h, h.cases_on (λ h, hxy h) (λ h, hyz h),
  sdiff_eq := λ x y, by { ext v w, refine ⟨λ h, ⟨h.1, ⟨_, h.2⟩⟩, λ h, ⟨h.1, h.2.2⟩⟩,
                          rintro rfl, exact x.irrefl h.1 },
  sup_inf_sdiff := λ a b, by { ext v w, refine ⟨λ h, _, λ h', _⟩,
                               obtain ⟨ha, _⟩|⟨ha, _⟩ := h; exact ha,
                               by_cases b.adj v w; exact or.inl ⟨h', h⟩ <|> exact or.inr ⟨h', h⟩ },
  inf_inf_sdiff := λ a b, by { ext v w, exact ⟨λ ⟨⟨_, hb⟩,⟨_, hb'⟩⟩, hb' hb, λ h, h.elim⟩ },
  le_sup_left := λ x y v w h, or.inl h,
  le_sup_right := λ x y v w h, or.inr h,
  le_inf := λ x y z hxy hyz v w h, ⟨hxy h, hyz h⟩,
  le_sup_inf := λ a b c v w h, or.dcases_on h.2 or.inl $
    or.dcases_on h.1 (λ h _, or.inl h) $ λ hb hc, or.inr ⟨hb, hc⟩,
  inf_compl_le_bot := λ a v w h, false.elim $ h.2.2 h.1,
  top_le_sup_compl := λ a v w ne, by { by_cases a.adj v w, exact or.inl h, exact or.inr ⟨ne, h⟩ },
  inf_le_left := λ x y v w h, h.1,
  inf_le_right := λ x y v w h, h.2,
  .. partial_order.lift adj ext }

@[simp] lemma top_adj (v w : V) : (⊤ : simple_graph V).adj v w ↔ v ≠ w := iff.rfl

@[simp] lemma bot_adj (v w : V) : (⊥ : simple_graph V).adj v w ↔ false := iff.rfl

@[simp] lemma complete_graph_eq_top (V : Type u) : complete_graph V = ⊤ := rfl

@[simp] lemma empty_graph_eq_bot (V : Type u) : empty_graph V = ⊥ := rfl

instance (V : Type u) : inhabited (simple_graph V) := ⟨⊤⟩

section decidable

variables (V) (H : simple_graph V) [decidable_rel G.adj] [decidable_rel H.adj]

instance bot.adj_decidable   : decidable_rel (⊥ : simple_graph V).adj := λ v w, decidable.false

instance sup.adj_decidable   : decidable_rel (G ⊔ H).adj := λ v w, or.decidable

instance inf.adj_decidable   : decidable_rel (G ⊓ H).adj := λ v w, and.decidable

instance sdiff.adj_decidable : decidable_rel (G \ H).adj := λ v w, and.decidable

variable [decidable_eq V]

instance top.adj_decidable   : decidable_rel (⊤ : simple_graph V).adj :=  λ v w, not.decidable

instance compl.adj_decidable : decidable_rel Gᶜ.adj := λ v w, and.decidable

end decidable

end order

/-- `G.support` is the set of vertices that form edges in `G`. -/
def support : set V := rel.dom G.adj

lemma mem_support {v : V} : v ∈ G.support ↔ ∃ w, G.adj v w := iff.rfl

lemma support_mono {G G' : simple_graph V} (h : G ≤ G') : G.support ⊆ G'.support :=
rel.dom_mono h

/-- `G.neighbor_set v` is the set of vertices adjacent to `v` in `G`. -/
def neighbor_set (v : V) : set V := set_of (G.adj v)

instance neighbor_set.mem_decidable (v : V) [decidable_rel G.adj] :
  decidable_pred (∈ G.neighbor_set v) := by { unfold neighbor_set, apply_instance }

/--
The edges of G consist of the unordered pairs of vertices related by
`G.adj`.

The way `edge_set` is defined is such that `mem_edge_set` is proved by `refl`.
(That is, `⟦(v, w)⟧ ∈ G.edge_set` is definitionally equal to `G.adj v w`.)
-/
def edge_set : set (sym2 V) := sym2.from_rel G.symm

@[simp] lemma mem_edge_set : ⟦(v, w)⟧ ∈ G.edge_set ↔ G.adj v w := iff.rfl

/--
Two vertices are adjacent iff there is an edge between them. The
condition `v ≠ w` ensures they are different endpoints of the edge,
which is necessary since when `v = w` the existential
`∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e` is satisfied by every edge
incident to `v`.
-/
lemma adj_iff_exists_edge {v w : V} :
  G.adj v w ↔ v ≠ w ∧ ∃ (e ∈ G.edge_set), v ∈ e ∧ w ∈ e :=
begin
  refine ⟨λ _, ⟨G.ne_of_adj ‹_›, ⟦(v,w)⟧, _⟩, _⟩,
  { simpa },
  { rintro ⟨hne, e, he, hv⟩,
    rw sym2.mem_and_mem_iff hne at hv,
    subst e,
    rwa mem_edge_set at he }
end

lemma adj_iff_exists_edge_coe : G.adj a b ↔ ∃ (e : G.edge_set), ↑e = ⟦(a, b)⟧ :=
by simp only [mem_edge_set, exists_prop, set_coe.exists, exists_eq_right, subtype.coe_mk]

lemma edge_other_ne {e : sym2 V} (he : e ∈ G.edge_set) {v : V} (h : v ∈ e) : h.other ≠ v :=
begin
  erw [← sym2.other_spec h, sym2.eq_swap] at he,
  exact G.ne_of_adj he,
end

instance decidable_mem_edge_set [decidable_rel G.adj] :
  decidable_pred (∈ G.edge_set) := sym2.from_rel.decidable_pred _

instance edges_fintype [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  fintype G.edge_set := subtype.fintype _

/-! ### Incidence set -/

/-- Set of edges incident to a given vertex, aka incidence set. -/
def incidence_set (v : V) : set (sym2 V) := {e ∈ G.edge_set | v ∈ e}

lemma incidence_set_subset (v : V) : G.incidence_set v ⊆ G.edge_set := λ _ h, h.1

lemma mk_mem_incidence_set_iff : ⟦(b, c)⟧ ∈ G.incidence_set a ↔ G.adj b c ∧ (a = b ∨ a = c) :=
and_congr_right' sym2.mem_iff

lemma mk_mem_incidence_set_left_iff : ⟦(a, b)⟧ ∈ G.incidence_set a ↔ G.adj a b :=
and_iff_left $ sym2.mem_mk_left _ _

lemma mk_mem_incidence_set_right_iff : ⟦(a, b)⟧ ∈ G.incidence_set b ↔ G.adj a b :=
and_iff_left $ sym2.mem_mk_right _ _

lemma edge_mem_incidence_set_iff {e : G.edge_set} : ↑e ∈ G.incidence_set a ↔ a ∈ (e : sym2 V) :=
and_iff_right e.2

lemma incidence_set_inter_incidence_set_subset (h : a ≠ b) :
  G.incidence_set a ∩ G.incidence_set b ⊆ {⟦(a, b)⟧} :=
λ e he, (sym2.mem_and_mem_iff h).1 ⟨he.1.2, he.2.2⟩

lemma incidence_set_inter_incidence_set (h : G.adj a b) :
  G.incidence_set a ∩ G.incidence_set b = {⟦(a, b)⟧} :=
begin
  refine (G.incidence_set_inter_incidence_set_subset $ h.ne).antisymm _,
  rintro _ (rfl : _ = ⟦(a, b)⟧),
  exact ⟨G.mk_mem_incidence_set_left_iff.2 h, G.mk_mem_incidence_set_right_iff.2 h⟩,
end

lemma adj_of_mem_incidence_set (h : a ≠ b) (ha : e ∈ G.incidence_set a)
  (hb : e ∈ G.incidence_set b) :
  G.adj a b :=
by rwa [←mk_mem_incidence_set_left_iff,
  ←set.mem_singleton_iff.1 $ G.incidence_set_inter_incidence_set_subset h ⟨ha, hb⟩]

instance decidable_mem_incidence_set [decidable_eq V] [decidable_rel G.adj] (v : V) :
  decidable_pred (∈ G.incidence_set v) := λ e, and.decidable

/--
The `edge_set` of the graph as a `finset`.
-/
def edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] : finset (sym2 V) :=
set.to_finset G.edge_set

@[simp] lemma mem_edge_finset [decidable_eq V] [fintype V] [decidable_rel G.adj] (e : sym2 V) :
  e ∈ G.edge_finset ↔ e ∈ G.edge_set :=
set.mem_to_finset

@[simp] lemma edge_set_univ_card [decidable_eq V] [fintype V] [decidable_rel G.adj] :
  (univ : finset G.edge_set).card = G.edge_finset.card :=
fintype.card_of_subtype G.edge_finset (mem_edge_finset _)

@[simp] lemma mem_neighbor_set (v w : V) : w ∈ G.neighbor_set v ↔ G.adj v w :=
iff.rfl

@[simp] lemma mem_neighbor_set' (v w : V) : G.neighbor_set v w ↔ G.adj v w :=
iff.rfl

@[simp] lemma mem_incidence_set (v w : V) : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ G.adj v w :=
by simp [incidence_set]

lemma mem_incidence_iff_neighbor {v w : V} : ⟦(v, w)⟧ ∈ G.incidence_set v ↔ w ∈ G.neighbor_set v :=
by simp only [mem_incidence_set, mem_neighbor_set]

lemma adj_incidence_set_inter {v : V} {e : sym2 V} (he : e ∈ G.edge_set) (h : v ∈ e) :
  G.incidence_set v ∩ G.incidence_set h.other = {e} :=
begin
  ext e',
  simp only [incidence_set, set.mem_sep_eq, set.mem_inter_eq, set.mem_singleton_iff],
  refine ⟨λ h', _, _⟩,
  { rw ←sym2.other_spec h,
    exact (sym2.mem_and_mem_iff (edge_other_ne G he h).symm).mp ⟨h'.1.2, h'.2.2⟩ },
  { rintro rfl,
    exact ⟨⟨he, h⟩, he, sym2.other_mem _⟩ }
end

lemma compl_neighbor_set_disjoint (G : simple_graph V) (v : V) :
  disjoint (G.neighbor_set v) (Gᶜ.neighbor_set v) :=
begin
  rw set.disjoint_iff,
  rintro w ⟨h, h'⟩,
  rw [mem_neighbor_set, compl_adj] at h',
  exact h'.2 h,
end

lemma neighbor_set_union_compl_neighbor_set_eq (G : simple_graph V) (v : V) :
  G.neighbor_set v ∪ Gᶜ.neighbor_set v = {v}ᶜ :=
begin
  ext w,
  have h := @ne_of_adj _ G,
  simp_rw [set.mem_union, mem_neighbor_set, compl_adj, set.mem_compl_eq, set.mem_singleton_iff],
  tauto,
end

-- TODO find out why TC inference has `h` failing a defeq check for `to_finset`
lemma card_neighbor_set_union_compl_neighbor_set [fintype V] (G : simple_graph V)
  (v : V) [h : fintype (G.neighbor_set v ∪ Gᶜ.neighbor_set v : set V)] :
  (@set.to_finset _ (G.neighbor_set v ∪ Gᶜ.neighbor_set v) h).card = fintype.card V - 1 :=
begin
  classical,
  simp_rw [neighbor_set_union_compl_neighbor_set_eq, set.to_finset_compl, finset.card_compl,
    set.to_finset_card, set.card_singleton],
end

lemma neighbor_set_compl (G : simple_graph V) (v : V) :
  Gᶜ.neighbor_set v = (G.neighbor_set v)ᶜ \ {v} :=
by { ext w, simp [and_comm, eq_comm] }

/--
The set of common neighbors between two vertices `v` and `w` in a graph `G` is the
intersection of the neighbor sets of `v` and `w`.
-/
def common_neighbors (v w : V) : set V := G.neighbor_set v ∩ G.neighbor_set w

lemma common_neighbors_eq (v w : V) :
  G.common_neighbors v w = G.neighbor_set v ∩ G.neighbor_set w := rfl

lemma mem_common_neighbors {u v w : V} : u ∈ G.common_neighbors v w ↔ G.adj v u ∧ G.adj w u :=
iff.rfl

lemma common_neighbors_symm (v w : V) : G.common_neighbors v w = G.common_neighbors w v :=
set.inter_comm _ _

lemma not_mem_common_neighbors_left (v w : V) : v ∉ G.common_neighbors v w :=
λ h, ne_of_adj G h.1 rfl

lemma not_mem_common_neighbors_right (v w : V) : w ∉ G.common_neighbors v w :=
λ h, ne_of_adj G h.2 rfl

lemma common_neighbors_subset_neighbor_set_left (v w : V) :
  G.common_neighbors v w ⊆ G.neighbor_set v :=
set.inter_subset_left _ _

lemma common_neighbors_subset_neighbor_set_right (v w : V) :
  G.common_neighbors v w ⊆ G.neighbor_set w :=
set.inter_subset_right _ _

instance decidable_mem_common_neighbors [decidable_rel G.adj] (v w : V) :
  decidable_pred (∈ G.common_neighbors v w) :=
λ a, and.decidable

lemma common_neighbors_top_eq {v w : V} :
  (⊤ : simple_graph V).common_neighbors v w = set.univ \ {v, w} :=
by { ext u, simp [common_neighbors, eq_comm, not_or_distrib.symm] }

section incidence
variable [decidable_eq V]

/--
Given an edge incident to a particular vertex, get the other vertex on the edge.
-/
def other_vertex_of_incident {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) : V := h.2.other'

lemma edge_other_incident_set {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  e ∈ G.incidence_set (G.other_vertex_of_incident h) :=
by { use h.1, simp [other_vertex_of_incident, sym2.other_mem'] }

lemma incidence_other_prop {v : V} {e : sym2 V} (h : e ∈ G.incidence_set v) :
  G.other_vertex_of_incident h ∈ G.neighbor_set v :=
by { cases h with he hv, rwa [←sym2.other_spec' hv, mem_edge_set] at he }

@[simp]
lemma incidence_other_neighbor_edge {v w : V} (h : w ∈ G.neighbor_set v) :
  G.other_vertex_of_incident (G.mem_incidence_iff_neighbor.mpr h) = w :=
sym2.congr_right.mp (sym2.other_spec' (G.mem_incidence_iff_neighbor.mpr h).right)

/--
There is an equivalence between the set of edges incident to a given
vertex and the set of vertices adjacent to the vertex.
-/
@[simps] def incidence_set_equiv_neighbor_set (v : V) : G.incidence_set v ≃ G.neighbor_set v :=
{ to_fun := λ e, ⟨G.other_vertex_of_incident e.2, G.incidence_other_prop e.2⟩,
  inv_fun := λ w, ⟨⟦(v, w.1)⟧, G.mem_incidence_iff_neighbor.mpr w.2⟩,
  left_inv := λ x, by simp [other_vertex_of_incident],
  right_inv := λ ⟨w, hw⟩, by simp }

end incidence

/-! ## Edge deletion -/

/-- Given a set of vertex pairs, remove all of the corresponding edges from the edge set.
It is fine to delete edges outside the edge set. -/
def delete_edges (s : set (sym2 V)) : simple_graph V :=
{ adj := G.adj \ sym2.to_rel s,
  symm := λ a b, by simp [adj_comm, sym2.eq_swap] }

@[simp] lemma delete_edges_adj (s : set (sym2 V)) (v w : V) :
  (G.delete_edges s).adj v w ↔ G.adj v w ∧ ¬ ⟦(v, w)⟧ ∈ s := iff.rfl

lemma sdiff_eq_delete_edges (G G' : simple_graph V) :
  G \ G' = G.delete_edges G'.edge_set :=
by { ext, simp }

lemma compl_eq_delete_edges :
  Gᶜ = (⊤ : simple_graph V).delete_edges G.edge_set :=
by { ext, simp }

@[simp] lemma delete_edges_delete_edges (s s' : set (sym2 V)) :
  (G.delete_edges s).delete_edges s' = G.delete_edges (s ∪ s') :=
by { ext, simp [and_assoc, not_or_distrib] }

@[simp] lemma delete_edges_empty_eq : G.delete_edges ∅ = G :=
by { ext, simp }

@[simp] lemma delete_edges_univ_eq : G.delete_edges set.univ = ⊥ :=
by { ext, simp }

lemma delete_edges_le (s : set (sym2 V)) : G.delete_edges s ≤ G :=
by { intro, simp { contextual := tt } }

lemma delete_edges_le_of_le {s s' : set (sym2 V)} (h : s ⊆ s') :
  G.delete_edges s' ≤ G.delete_edges s :=
λ v w, begin
  simp only [delete_edges_adj, and_imp, true_and] { contextual := tt },
  exact λ ha hn hs, hn (h hs),
end

lemma delete_edges_eq_inter_edge_set (s : set (sym2 V)) :
  G.delete_edges s = G.delete_edges (s ∩ G.edge_set) :=
by { ext, simp [imp_false] { contextual := tt } }

section finite_at

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`fintype (G.neighbor_set v)`.

We define `G.neighbor_finset v` to be the `finset` version of `G.neighbor_set v`.
Use `neighbor_finset_eq_filter` to rewrite this definition as a `filter`.
-/

variables (v) [fintype (G.neighbor_set v)]
/--
`G.neighbors v` is the `finset` version of `G.adj v` in case `G` is
locally finite at `v`.
-/
def neighbor_finset : finset V := (G.neighbor_set v).to_finset

lemma neighbor_finset_def : G.neighbor_finset v = (G.neighbor_set v).to_finset := rfl

@[simp] lemma mem_neighbor_finset (w : V) :
  w ∈ G.neighbor_finset v ↔ G.adj v w :=
set.mem_to_finset

/--
`G.degree v` is the number of vertices adjacent to `v`.
-/
def degree : ℕ := (G.neighbor_finset v).card

@[simp]
lemma card_neighbor_set_eq_degree : fintype.card (G.neighbor_set v) = G.degree v :=
(set.to_finset_card _).symm

lemma degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.adj v w :=
by simp only [degree, card_pos, finset.nonempty, mem_neighbor_finset]

lemma degree_compl [fintype (Gᶜ.neighbor_set v)] [fintype V] :
  Gᶜ.degree v = fintype.card V - 1 - G.degree v :=
begin
  classical,
  rw [← card_neighbor_set_union_compl_neighbor_set G v, set.to_finset_union],
  simp [card_disjoint_union (set.to_finset_disjoint_iff.mpr (compl_neighbor_set_disjoint G v))],
end

instance incidence_set_fintype [decidable_eq V] : fintype (G.incidence_set v) :=
fintype.of_equiv (G.neighbor_set v) (G.incidence_set_equiv_neighbor_set v).symm

/--
This is the `finset` version of `incidence_set`.
-/
def incidence_finset [decidable_eq V] : finset (sym2 V) := (G.incidence_set v).to_finset

@[simp]
lemma card_incidence_set_eq_degree [decidable_eq V] :
  fintype.card (G.incidence_set v) = G.degree v :=
by { rw fintype.card_congr (G.incidence_set_equiv_neighbor_set v), simp }

@[simp]
lemma mem_incidence_finset [decidable_eq V] (e : sym2 V) :
  e ∈ G.incidence_finset v ↔ e ∈ G.incidence_set v :=
set.mem_to_finset

end finite_at

section locally_finite

/--
A graph is locally finite if every vertex has a finite neighbor set.
-/
@[reducible]
def locally_finite := Π (v : V), fintype (G.neighbor_set v)

variable [locally_finite G]

/--
A locally finite simple graph is regular of degree `d` if every vertex has degree `d`.
-/
def is_regular_of_degree (d : ℕ) : Prop := ∀ (v : V), G.degree v = d

variables {G}

lemma is_regular_of_degree.degree_eq {d : ℕ} (h : G.is_regular_of_degree d) (v : V) :
  G.degree v = d := h v

lemma is_regular_of_degree.compl [fintype V] [decidable_eq V]
  {G : simple_graph V} [decidable_rel G.adj]
  {k : ℕ} (h : G.is_regular_of_degree k) :
  Gᶜ.is_regular_of_degree (fintype.card V - 1 - k) :=
by { intro v, rw [degree_compl, h v] }

end locally_finite

section finite

variable [fintype V]

instance neighbor_set_fintype [decidable_rel G.adj] (v : V) : fintype (G.neighbor_set v) :=
@subtype.fintype _ _ (by { simp_rw mem_neighbor_set, apply_instance }) _

lemma neighbor_finset_eq_filter {v : V} [decidable_rel G.adj] :
  G.neighbor_finset v = finset.univ.filter (G.adj v) :=
by { ext, simp }

lemma neighbor_finset_compl [decidable_eq V] [decidable_rel G.adj] (v : V) :
  Gᶜ.neighbor_finset v = (G.neighbor_finset v)ᶜ \ {v} :=
by simp only [neighbor_finset, neighbor_set_compl, set.to_finset_sdiff, set.to_finset_compl,
    set.to_finset_singleton]

@[simp]
lemma complete_graph_degree [decidable_eq V] (v : V) :
  (⊤ : simple_graph V).degree v = fintype.card V - 1 :=
begin
  convert univ.card.pred_eq_sub_one,
  erw [degree, neighbor_finset_eq_filter, filter_ne, card_erase_of_mem (mem_univ v)],
end

lemma bot_degree (v : V) : (⊥ : simple_graph V).degree v = 0 :=
begin
  erw [degree, neighbor_finset_eq_filter, filter_false],
  exact finset.card_empty,
end

lemma is_regular_of_degree.top [decidable_eq V] :
  (⊤ : simple_graph V).is_regular_of_degree (fintype.card V - 1) :=
by { intro v, simp }

/--
The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `min_degree_le_degree`
and `le_min_degree_of_forall_le_degree`.
-/
def min_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ v, G.degree v)).min 0

/--
There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_minimal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.min_degree = G.degree v :=
begin
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht),
  refine ⟨v, by simp [min_degree, ht]⟩,
end

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
lemma min_degree_le_degree [decidable_rel G.adj] (v : V) : G.min_degree ≤ G.degree v :=
begin
  obtain ⟨t, ht⟩ := finset.min_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.min_le_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rw option.mem_def at ht,
  rwa [min_degree, ht, option.get_or_else_some],
end

/--
In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.min_degree` is
defined to be a natural.
-/
lemma le_min_degree_of_forall_le_degree [decidable_rel G.adj] [nonempty V] (k : ℕ)
  (h : ∀ v, k ≤ G.degree v) :
  k ≤ G.min_degree :=
by { rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩, rw hv, apply h }

/--
The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_max_degree`
and `max_degree_le_of_forall_degree_le`.
-/
def max_degree [decidable_rel G.adj] : ℕ :=
option.get_or_else (univ.image (λ v, G.degree v)).max 0

/--
There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex.
-/
lemma exists_maximal_degree_vertex [decidable_rel G.adj] [nonempty V] :
  ∃ v, G.max_degree = G.degree v :=
begin
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image (λ v, G.degree v)),
  have ht₂ := mem_of_max ht,
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂,
  rcases ht₂ with ⟨v, rfl⟩,
  rw option.mem_def at ht,
  refine ⟨v, _⟩,
  rw [max_degree, ht],
  refl
end

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
lemma degree_le_max_degree [decidable_rel G.adj] (v : V) : G.degree v ≤ G.max_degree :=
begin
  obtain ⟨t, ht : _ = _⟩ := finset.max_of_mem (mem_image_of_mem (λ v, G.degree v) (mem_univ v)),
  have := finset.le_max_of_mem (mem_image_of_mem _ (mem_univ v)) ht,
  rwa [max_degree, ht, option.get_or_else_some],
end

/--
In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree.
-/
lemma max_degree_le_of_forall_degree_le [decidable_rel G.adj] (k : ℕ)
  (h : ∀ v, G.degree v ≤ k) :
  G.max_degree ≤ k :=
begin
  by_cases hV : (univ : finset V).nonempty,
  { haveI : nonempty V := univ_nonempty_iff.mp hV,
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex,
    rw hv,
    apply h },
  { rw not_nonempty_iff_eq_empty at hV,
    rw [max_degree, hV, image_empty],
    exact zero_le k },
end

lemma degree_lt_card_verts [decidable_rel G.adj] (v : V) : G.degree v < fintype.card V :=
begin
  classical,
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  exact ⟨v, by simp, finset.subset_univ _⟩,
end

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero.
-/
lemma max_degree_lt_card_verts [decidable_rel G.adj] [nonempty V] : G.max_degree < fintype.card V :=
begin
  cases G.exists_maximal_degree_vertex with v hv,
  rw hv,
  apply G.degree_lt_card_verts v,
end

lemma card_common_neighbors_le_degree_left [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) ≤ G.degree v :=
begin
  rw [←card_neighbor_set_eq_degree],
  exact set.card_le_of_subset (set.inter_subset_left _ _),
end

lemma card_common_neighbors_le_degree_right [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) ≤ G.degree w :=
by simp_rw [common_neighbors_symm _ v w, card_common_neighbors_le_degree_left]

lemma card_common_neighbors_lt_card_verts [decidable_rel G.adj] (v w : V) :
  fintype.card (G.common_neighbors v w) < fintype.card V :=
nat.lt_of_le_of_lt (G.card_common_neighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/--
If the condition `G.adj v w` fails, then `card_common_neighbors_le_degree` is
the best we can do in general.
-/
lemma adj.card_common_neighbors_lt_degree {G : simple_graph V} [decidable_rel G.adj]
  {v w : V} (h : G.adj v w) :
  fintype.card (G.common_neighbors v w) < G.degree v :=
begin
  classical,
  erw [←set.to_finset_card],
  apply finset.card_lt_card,
  rw finset.ssubset_iff,
  use w,
  split,
  { rw set.mem_to_finset,
    apply not_mem_common_neighbors_right },
  { rw finset.insert_subset,
    split,
    { simpa, },
    { rw [neighbor_finset, ← set.subset_iff_to_finset_subset],
      exact G.common_neighbors_subset_neighbor_set_left _ _ } }
end

lemma card_common_neighbors_top [decidable_eq V] {v w : V} (h : v ≠ w) :
  fintype.card ((⊤ : simple_graph V).common_neighbors v w) = fintype.card V - 2 :=
begin
  simp only [common_neighbors_top_eq, ← set.to_finset_card, set.to_finset_sdiff],
  rw finset.card_sdiff,
  { simp [finset.card_univ, h], },
  { simp only [←set.subset_iff_to_finset_subset, set.subset_univ] },
end

end finite

section maps

/--
A graph homomorphism is a map on vertex sets that respects adjacency relations.

The notation `G →g G'` represents the type of graph homomorphisms.
-/
abbreviation hom := rel_hom G.adj G'.adj

/--
A graph embedding is an embedding `f` such that for vertices `v w : V`,
`G.adj f(v) f(w) ↔ G.adj v w `. Its image is an induced subgraph of G'.

The notation `G ↪g G'` represents the type of graph embeddings.
-/
abbreviation embedding := rel_embedding G.adj G'.adj

/--
A graph isomorphism is an bijective map on vertex sets that respects adjacency relations.

The notation `G ≃g G'` represents the type of graph isomorphisms.
-/
abbreviation iso := rel_iso G.adj G'.adj

infix ` →g ` : 50 := hom
infix ` ↪g ` : 50 := embedding
infix ` ≃g ` : 50 := iso

namespace hom
variables {G G'} (f : G →g G')

/-- The identity homomorphism from a graph to itself. -/
abbreviation id : G →g G := rel_hom.id _

lemma map_adj {v w : V} (h : G.adj v w) : G'.adj (f v) (f w) := f.map_rel' h

lemma map_mem_edge_set {e : sym2 V} (h : e ∈ G.edge_set) : e.map f ∈ G'.edge_set :=
quotient.ind (λ e h, sym2.from_rel_prop.mpr (f.map_rel' h)) e h

lemma apply_mem_neighbor_set {v w : V} (h : w ∈ G.neighbor_set v) : f w ∈ G'.neighbor_set (f v) :=
map_adj f h

/-- The map between edge sets induced by a homomorphism.
The underlying map on edges is given by `sym2.map`. -/
@[simps] def map_edge_set (e : G.edge_set) : G'.edge_set :=
⟨sym2.map f e, f.map_mem_edge_set e.property⟩

/-- The map between neighbor sets induced by a homomorphism. -/
@[simps] def map_neighbor_set (v : V) (w : G.neighbor_set v) : G'.neighbor_set (f v) :=
⟨f w, f.apply_mem_neighbor_set w.property⟩

/-- The induced map for spanning subgraphs, which is the identity on vertices. -/
def map_spanning_subgraphs {G G' : simple_graph V} (h : G ≤ G') : G →g G' :=
{ to_fun := λ x, x,
  map_rel' := h }

lemma map_edge_set.injective (hinj : function.injective f) : function.injective f.map_edge_set :=
begin
  rintros ⟨e₁, h₁⟩ ⟨e₂, h₂⟩,
  dsimp [hom.map_edge_set],
  repeat { rw subtype.mk_eq_mk },
  apply sym2.map.injective hinj,
end

variable {G'' : simple_graph X}

/-- Composition of graph homomorphisms. -/
abbreviation comp (f' : G' →g G'') (f : G →g G') : G →g G'' := f'.comp f

@[simp] lemma coe_comp (f' : G' →g G'') (f : G →g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end hom

namespace embedding
variables {G G'} (f : G ↪g G')

/-- The identity embedding from a graph to itself. -/
abbreviation refl : G ↪g G := rel_embedding.refl _

/-- An embedding of graphs gives rise to a homomorphism of graphs. -/
abbreviation to_hom : G →g G' := f.to_rel_hom

lemma map_adj_iff {v w : V} : G'.adj (f v) (f w) ↔ G.adj v w := f.map_rel_iff

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ G'.edge_set ↔ e ∈ G.edge_set :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e

lemma apply_mem_neighbor_set_iff {v w : V} : f w ∈ G'.neighbor_set (f v) ↔ w ∈ G.neighbor_set v :=
map_adj_iff f

/-- A graph embedding induces an embedding of edge sets. -/
@[simps] def map_edge_set : G.edge_set ↪ G'.edge_set :=
{ to_fun := hom.map_edge_set f,
  inj' := hom.map_edge_set.injective f f.inj' }

/-- A graph embedding induces an embedding of neighbor sets. -/
@[simps] def map_neighbor_set (v : V) : G.neighbor_set v ↪ G'.neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inj' := begin
    rintros ⟨w₁, h₁⟩ ⟨w₂, h₂⟩ h,
    rw subtype.mk_eq_mk at h ⊢,
    exact f.inj' h,
  end }

/-- Embeddings of types induce embeddings of complete graphs on those types. -/
def complete_graph.of_embedding {α β : Type*} (f : α ↪ β) : complete_graph α ↪g complete_graph β :=
{ to_fun := f,
  inj' := f.inj',
  map_rel_iff' := by simp }

variables {G'' : simple_graph X}

/-- Composition of graph embeddings. -/
abbreviation comp (f' : G' ↪g G'') (f : G ↪g G') : G ↪g G'' := f.trans f'

@[simp] lemma coe_comp (f' : G' ↪g G'') (f : G ↪g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end embedding

namespace iso
variables {G G'} (f : G ≃g G')

/-- The identity isomorphism of a graph with itself. -/
abbreviation refl : G ≃g G := rel_iso.refl _

/-- An isomorphism of graphs gives rise to an embedding of graphs. -/
abbreviation to_embedding : G ↪g G' := f.to_rel_embedding

/-- An isomorphism of graphs gives rise to a homomorphism of graphs. -/
abbreviation to_hom : G →g G' := f.to_embedding.to_hom

/-- The inverse of a graph isomorphism. --/
abbreviation symm : G' ≃g G := f.symm

lemma map_adj_iff {v w : V} : G'.adj (f v) (f w) ↔ G.adj v w := f.map_rel_iff

lemma map_mem_edge_set_iff {e : sym2 V} : e.map f ∈ G'.edge_set ↔ e ∈ G.edge_set :=
quotient.ind (λ ⟨v, w⟩, f.map_adj_iff) e

lemma apply_mem_neighbor_set_iff {v w : V} : f w ∈ G'.neighbor_set (f v) ↔ w ∈ G.neighbor_set v :=
map_adj_iff f

/-- An isomorphism of graphs induces an equivalence of edge sets. -/
@[simps] def map_edge_set : G.edge_set ≃ G'.edge_set :=
{ to_fun := hom.map_edge_set f,
  inv_fun := hom.map_edge_set f.symm,
  left_inv := begin
    rintro ⟨e, h⟩,
    simp only [hom.map_edge_set, sym2.map_map, rel_iso.coe_coe_fn,
      rel_embedding.coe_coe_fn, subtype.mk_eq_mk, subtype.coe_mk, coe_coe],
    apply congr_fun,
    convert sym2.map_id,
    exact funext (λ _, rel_iso.symm_apply_apply _ _),
  end,
  right_inv := begin
    rintro ⟨e, h⟩,
    simp only [hom.map_edge_set, sym2.map_map, rel_iso.coe_coe_fn,
      rel_embedding.coe_coe_fn, subtype.mk_eq_mk, subtype.coe_mk, coe_coe],
    apply congr_fun,
    convert sym2.map_id,
    exact funext (λ _, rel_iso.apply_symm_apply _ _),
  end }

/-- A graph isomorphism induces an equivalence of neighbor sets. -/
@[simps] def map_neighbor_set (v : V) : G.neighbor_set v ≃ G'.neighbor_set (f v) :=
{ to_fun := λ w, ⟨f w, f.apply_mem_neighbor_set_iff.mpr w.2⟩,
  inv_fun := λ w, ⟨f.symm w, begin
    convert f.symm.apply_mem_neighbor_set_iff.mpr w.2,
    simp only [rel_iso.symm_apply_apply],
  end⟩,
  left_inv := λ w, by simp,
  right_inv := λ w, by simp }

lemma card_eq_of_iso [fintype V] [fintype W] (f : G ≃g G') : fintype.card V = fintype.card W :=
by convert (fintype.of_equiv_card f.to_equiv).symm

variables {G'' : simple_graph X}

/-- Composition of graph isomorphisms. -/
abbreviation comp (f' : G' ≃g G'') (f : G ≃g G') : G ≃g G'' := f.trans f'

@[simp] lemma coe_comp (f' : G' ≃g G'') (f : G ≃g G') : ⇑(f'.comp f) = f' ∘ f := rfl

end iso

end maps

end simple_graph
