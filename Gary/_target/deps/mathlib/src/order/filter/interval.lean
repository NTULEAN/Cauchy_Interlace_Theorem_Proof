/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.set.intervals.ord_connected
import order.filter.lift
import order.filter.at_top_bot

/-!
# Convergence of intervals

If both `a` and `b` tend to some filter `l₁`, sometimes this implies that `Ixx a b` tends to
`l₂.lift' powerset`, i.e., for any `s ∈ l₂` eventually `Ixx a b` becomes a subset of `s`.  Here and
below `Ixx` is one of `Icc`, `Ico`, `Ioc`, and `Ioo`. We define `filter.tendsto_Ixx_class Ixx l₁ l₂`
to be a typeclass representing this property.

The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but sometimes we can
drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic a) (𝓟 $ Iio a)`,
i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁ n) (u₂ n)` is
eventually included in `Iio a`.

The next table shows “output” filters `l₂` for different values of `Ixx` and `l₁`. The instances
that need topology are defined in `topology/algebra/ordered`.

| Input filter |  `Ixx = Icc`  |  `Ixx = Ico`  |  `Ixx = Ioc`  |  `Ixx = Ioo`  |
| -----------: | :-----------: | :-----------: | :-----------: | :-----------: |
|     `at_top` |    `at_top`   |    `at_top`   |    `at_top`   |    `at_top`   |
|     `at_bot` |    `at_bot`   |    `at_bot`   |    `at_bot`   |    `at_bot`   |
|     `pure a` |    `pure a`   |      `⊥`      |      `⊥`      |      `⊥`      |
|  `𝓟 (Iic a)` |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iic a)`  |  `𝓟 (Iio a)`  |
|  `𝓟 (Ici a)` |  `𝓟 (Ici a)`  |  `𝓟 (Ici a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Ioi a)` |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |  `𝓟 (Ioi a)`  |
|  `𝓟 (Iio a)` |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |  `𝓟 (Iio a)`  |
|        `𝓝 a` |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |     `𝓝 a`     |
| `𝓝[Iic a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |  `𝓝[Iic a] b` |  `𝓝[Iio a] b` |
| `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ici a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |  `𝓝[Ioi a] b` |
| `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |  `𝓝[Iio a] b` |

-/

variables {α β : Type*}

open_locale classical filter interval

open set function

namespace filter

section preorder

variables [preorder α]

/-- A pair of filters `l₁`, `l₂` has `tendsto_Ixx_class Ixx` property if `Ixx a b` tends to
`l₂.lift' powerset` as `a` and `b` tend to `l₁`. In all instances `Ixx` is one of `Icc`, `Ico`,
`Ioc`, or `Ioo`. The instances provide the best `l₂` for a given `l₁`. In many cases `l₁ = l₂` but
sometimes we can drop an endpoint from an interval: e.g., we prove `tendsto_Ixx_class Ico (𝓟 $ Iic
a) (𝓟 $ Iio a)`, i.e., if `u₁ n` and `u₂ n` belong eventually to `Iic a`, then the interval `Ico (u₁
n) (u₂ n)` is eventually included in `Iio a`.

We mark `l₂` as an `out_param` so that Lean can automatically find an appropriate `l₂` based on
`Ixx` and `l₁`. This way, e.g., `tendsto.Ico h₁ h₂` works without specifying explicitly `l₂`. -/
class tendsto_Ixx_class (Ixx : α → α → set α) (l₁ : filter α) (l₂ : out_param $ filter α) : Prop :=
(tendsto_Ixx : tendsto (λ p : α × α, Ixx p.1 p.2) (l₁ ×ᶠ l₁) (l₂.lift' powerset))

lemma tendsto.Icc {l₁ l₂ : filter α} [tendsto_Ixx_class Icc l₁ l₂]
  {lb : filter β} {u₁ u₂ : β → α} (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
  tendsto (λ x, Icc (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
tendsto_Ixx_class.tendsto_Ixx.comp $ h₁.prod_mk h₂

lemma tendsto.Ioc {l₁ l₂ : filter α} [tendsto_Ixx_class Ioc l₁ l₂]
  {lb : filter β} {u₁ u₂ : β → α} (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
  tendsto (λ x, Ioc (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
tendsto_Ixx_class.tendsto_Ixx.comp $ h₁.prod_mk h₂

lemma tendsto.Ico {l₁ l₂ : filter α} [tendsto_Ixx_class Ico l₁ l₂]
  {lb : filter β} {u₁ u₂ : β → α} (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
  tendsto (λ x, Ico (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
tendsto_Ixx_class.tendsto_Ixx.comp $ h₁.prod_mk h₂

lemma tendsto.Ioo {l₁ l₂ : filter α} [tendsto_Ixx_class Ioo l₁ l₂]
  {lb : filter β} {u₁ u₂ : β → α} (h₁ : tendsto u₁ lb l₁) (h₂ : tendsto u₂ lb l₁) :
  tendsto (λ x, Ioo (u₁ x) (u₂ x)) lb (l₂.lift' powerset) :=
tendsto_Ixx_class.tendsto_Ixx.comp $ h₁.prod_mk h₂

lemma tendsto_Ixx_class_principal {s t : set α} {Ixx : α → α → set α} :
  tendsto_Ixx_class Ixx (𝓟 s) (𝓟 t) ↔ ∀ (x ∈ s) (y ∈ s), Ixx x y ⊆ t :=
begin
  refine iff.trans ⟨λ h, h.1, λ h, ⟨h⟩⟩ _,
  simp [lift'_principal monotone_powerset, -mem_prod, -prod.forall, forall_prod_set]
end

lemma tendsto_Ixx_class_inf {l₁ l₁' l₂ l₂' : filter α} {Ixx}
  [h : tendsto_Ixx_class Ixx l₁ l₂] [h' : tendsto_Ixx_class Ixx l₁' l₂'] :
  tendsto_Ixx_class Ixx (l₁ ⊓ l₁') (l₂ ⊓ l₂') :=
⟨by simpa only [prod_inf_prod, lift'_inf_powerset] using h.1.inf h'.1⟩

lemma tendsto_Ixx_class_of_subset {l₁ l₂ : filter α} {Ixx Ixx' : α → α → set α}
  (h : ∀ a b, Ixx a b ⊆ Ixx' a b) [h' : tendsto_Ixx_class Ixx' l₁ l₂] :
  tendsto_Ixx_class Ixx l₁ l₂ :=
⟨tendsto_lift'_powerset_mono h'.1 $ eventually_of_forall $ prod.forall.2 h⟩

lemma has_basis.tendsto_Ixx_class {ι : Type*} {p : ι → Prop} {s} {l : filter α}
  (hl : l.has_basis p s) {Ixx : α → α → set α}
  (H : ∀ i, p i → ∀ (x ∈ s i) (y ∈ s i), Ixx x y ⊆ s i) :
  tendsto_Ixx_class Ixx l l :=
⟨(hl.prod_self.tendsto_iff (hl.lift' monotone_powerset)).2 $ λ i hi,
  ⟨i, hi, λ x hx, H i hi _ hx.1 _ hx.2⟩⟩

instance tendsto_Icc_at_top_at_top : tendsto_Ixx_class Icc (at_top : filter α) at_top :=
(has_basis_infi_principal_finite _).tendsto_Ixx_class $ λ s hs,
set.ord_connected.out $ ord_connected_bInter $ λ i hi, ord_connected_Ici

instance tendsto_Ico_at_top_at_top : tendsto_Ixx_class Ico (at_top : filter α) at_top :=
tendsto_Ixx_class_of_subset (λ _ _, Ico_subset_Icc_self)

instance tendsto_Ioc_at_top_at_top : tendsto_Ixx_class Ioc (at_top : filter α) at_top :=
tendsto_Ixx_class_of_subset (λ _ _, Ioc_subset_Icc_self)

instance tendsto_Ioo_at_top_at_top : tendsto_Ixx_class Ioo (at_top : filter α) at_top :=
tendsto_Ixx_class_of_subset (λ _ _, Ioo_subset_Icc_self)

instance tendsto_Icc_at_bot_at_bot : tendsto_Ixx_class Icc (at_bot : filter α) at_bot :=
(has_basis_infi_principal_finite _).tendsto_Ixx_class $ λ s hs,
set.ord_connected.out $ ord_connected_bInter $ λ i hi, ord_connected_Iic

instance tendsto_Ico_at_bot_at_bot : tendsto_Ixx_class Ico (at_bot : filter α) at_bot :=
tendsto_Ixx_class_of_subset (λ _ _, Ico_subset_Icc_self)

instance tendsto_Ioc_at_bot_at_bot : tendsto_Ixx_class Ioc (at_bot : filter α) at_bot :=
tendsto_Ixx_class_of_subset (λ _ _, Ioc_subset_Icc_self)

instance tendsto_Ioo_at_bot_at_bot : tendsto_Ixx_class Ioo (at_bot : filter α) at_bot :=
tendsto_Ixx_class_of_subset (λ _ _, Ioo_subset_Icc_self)

instance ord_connected.tendsto_Icc {s : set α} [hs : ord_connected s] :
  tendsto_Ixx_class Icc (𝓟 s) (𝓟 s) :=
tendsto_Ixx_class_principal.2 hs.out

instance tendsto_Ico_Ici_Ici {a : α} : tendsto_Ixx_class Ico (𝓟 (Ici a)) (𝓟 (Ici a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ico_subset_Icc_self)

instance tendsto_Ico_Ioi_Ioi {a : α} : tendsto_Ixx_class Ico (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ico_subset_Icc_self)

instance tendsto_Ico_Iic_Iio {a : α} : tendsto_Ixx_class Ico (𝓟 (Iic a)) (𝓟 (Iio a)) :=
tendsto_Ixx_class_principal.2 $ λ a ha b hb x hx, lt_of_lt_of_le hx.2 hb

instance tendsto_Ico_Iio_Iio {a : α} : tendsto_Ixx_class Ico (𝓟 (Iio a)) (𝓟 (Iio a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ico_subset_Icc_self)

instance tendsto_Ioc_Ici_Ioi {a : α} : tendsto_Ixx_class Ioc (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
tendsto_Ixx_class_principal.2 $ λ x hx y hy t ht, lt_of_le_of_lt hx ht.1

instance tendsto_Ioc_Iic_Iic {a : α} : tendsto_Ixx_class Ioc (𝓟 (Iic a)) (𝓟 (Iic a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ioc_subset_Icc_self)

instance tendsto_Ioc_Iio_Iio {a : α} : tendsto_Ixx_class Ioc (𝓟 (Iio a)) (𝓟 (Iio a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ioc_subset_Icc_self)

instance tendsto_Ioc_Ioi_Ioi {a : α} : tendsto_Ixx_class Ioc (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ioc_subset_Icc_self)

instance tendsto_Ioo_Ici_Ioi {a : α} : tendsto_Ixx_class Ioo (𝓟 (Ici a)) (𝓟 (Ioi a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ioo_subset_Ioc_self)

instance tendsto_Ioo_Iic_Iio {a : α} : tendsto_Ixx_class Ioo (𝓟 (Iic a)) (𝓟 (Iio a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ioo_subset_Ico_self)

instance tendsto_Ioo_Ioi_Ioi {a : α} : tendsto_Ixx_class Ioo (𝓟 (Ioi a)) (𝓟 (Ioi a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ioo_subset_Ioc_self)

instance tendsto_Ioo_Iio_Iio {a : α} : tendsto_Ixx_class Ioo (𝓟 (Iio a)) (𝓟 (Iio a)) :=
tendsto_Ixx_class_of_subset (λ _ _, Ioo_subset_Ioc_self)

instance tendsto_Icc_Icc_Icc {a b : α} :
  tendsto_Ixx_class Icc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
tendsto_Ixx_class_principal.mpr $ λ x hx y hy, Icc_subset_Icc hx.1 hy.2

instance tendsto_Ioc_Icc_Icc {a b : α} : tendsto_Ixx_class Ioc (𝓟 (Icc a b)) (𝓟 (Icc a b)) :=
tendsto_Ixx_class_of_subset $ λ _ _, Ioc_subset_Icc_self

end preorder

section partial_order

variable [partial_order α]

instance tendsto_Icc_pure_pure {a : α} : tendsto_Ixx_class Icc (pure a) (pure a : filter α) :=
by { rw ← principal_singleton, exact tendsto_Ixx_class_principal.2 ord_connected_singleton.out }

instance tendsto_Ico_pure_bot {a : α} : tendsto_Ixx_class Ico (pure a) ⊥ :=
⟨by simp [lift'_bot monotone_powerset]⟩

instance tendsto_Ioc_pure_bot {a : α} : tendsto_Ixx_class Ioc (pure a) ⊥ :=
⟨by simp [lift'_bot monotone_powerset]⟩

instance tendsto_Ioo_pure_bot {a : α} : tendsto_Ixx_class Ioo (pure a) ⊥ :=
tendsto_Ixx_class_of_subset (λ _ _, Ioo_subset_Ioc_self)

end partial_order

section linear_order

variables [linear_order α]

instance tendsto_Icc_interval_interval {a b : α} : tendsto_Ixx_class Icc (𝓟 [a, b]) (𝓟 [a, b]) :=
filter.tendsto_Icc_Icc_Icc

instance tendsto_Ioc_interval_interval {a b : α} : tendsto_Ixx_class Ioc (𝓟 [a, b]) (𝓟 [a, b]) :=
filter.tendsto_Ioc_Icc_Icc

instance tendsto_interval_of_Icc {l : filter α} [tendsto_Ixx_class Icc l l] :
  tendsto_Ixx_class interval l l :=
begin
  refine ⟨λ s hs, mem_map.2 $ mem_prod_self_iff.2 _⟩,
  obtain ⟨t, htl, hts⟩ : ∃ t ∈ l, ∀ p ∈ (t : set α) ×ˢ t, Icc (p : α × α).1 p.2 ∈ s,
    from mem_prod_self_iff.1 (mem_map.1 (tendsto_fst.Icc tendsto_snd hs)),
  refine ⟨t, htl, λ p hp, _⟩,
  cases le_total p.1 p.2,
  { rw [mem_preimage, interval_of_le h], exact hts p hp },
  { rw [mem_preimage, interval_of_ge h], exact hts ⟨p.2, p.1⟩ ⟨hp.2, hp.1⟩ }
end

lemma tendsto.interval {l : filter α} [tendsto_Ixx_class Icc l l] {f g : β → α} {lb : filter β}
  (hf : tendsto f lb l) (hg : tendsto g lb l) :
  tendsto (λ x, [f x, g x]) lb (l.lift' powerset) :=
tendsto_Ixx_class.tendsto_Ixx.comp $ hf.prod_mk hg

end linear_order

end filter
