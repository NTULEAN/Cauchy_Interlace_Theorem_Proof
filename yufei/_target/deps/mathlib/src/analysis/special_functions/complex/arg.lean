/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
import analysis.special_functions.trigonometric.angle
import analysis.special_functions.trigonometric.inverse

/-!
# The argument of a complex number.

We define `arg : ℂ → ℝ`, returing a real number in the range (-π, π],
such that for `x ≠ 0`, `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
while `arg 0` defaults to `0`
-/

noncomputable theory

namespace complex

open_locale complex_conjugate real topological_space
open filter set

/-- `arg` returns values in the range (-π, π], such that for `x ≠ 0`,
  `sin (arg x) = x.im / x.abs` and `cos (arg x) = x.re / x.abs`,
  `arg 0` defaults to `0` -/
noncomputable def arg (x : ℂ) : ℝ :=
if 0 ≤ x.re
then real.arcsin (x.im / x.abs)
else if 0 ≤ x.im
then real.arcsin ((-x).im / x.abs) + π
else real.arcsin ((-x).im / x.abs) - π

lemma sin_arg (x : ℂ) : real.sin (arg x) = x.im / x.abs :=
by unfold arg; split_ifs;
  simp [sub_eq_add_neg, arg, real.sin_arcsin (abs_le.1 (abs_im_div_abs_le_one x)).1
    (abs_le.1 (abs_im_div_abs_le_one x)).2, real.sin_add, neg_div, real.arcsin_neg,
    real.sin_neg]

lemma cos_arg {x : ℂ} (hx : x ≠ 0) : real.cos (arg x) = x.re / x.abs :=
begin
  have habs : 0 < abs x := abs_pos.2 hx,
  have him : |im x / abs x| ≤ 1,
  { rw [_root_.abs_div, abs_abs], exact div_le_one_of_le x.abs_im_le_abs x.abs_nonneg },
  rw abs_le at him,
  rw arg, split_ifs with h₁ h₂ h₂,
  { rw [real.cos_arcsin]; field_simp [real.sqrt_sq, habs.le, *] },
  { rw [real.cos_add_pi, real.cos_arcsin],
    { field_simp [real.sqrt_div (sq_nonneg _), real.sqrt_sq_eq_abs,
        _root_.abs_of_neg (not_le.1 h₁), *] },
    { simpa [neg_div] using him.2 },
    { simpa [neg_div, neg_le] using him.1 } },
  { rw [real.cos_sub_pi, real.cos_arcsin],
    { field_simp [real.sqrt_div (sq_nonneg _), real.sqrt_sq_eq_abs,
        _root_.abs_of_neg (not_le.1 h₁), *] },
    { simpa [neg_div] using him.2 },
    { simpa [neg_div, neg_le] using him.1 } }
end

@[simp] lemma abs_mul_exp_arg_mul_I (x : ℂ) : ↑(abs x) * exp (arg x * I) = x :=
begin
  rcases eq_or_ne x 0 with (rfl|hx),
  { simp },
  { have : abs x ≠ 0 := abs_ne_zero.2 hx,
    ext; field_simp [sin_arg, cos_arg hx, this, mul_comm (abs x)] }
end

@[simp] lemma abs_mul_cos_add_sin_mul_I (x : ℂ) :
  (abs x * (cos (arg x) + sin (arg x) * I) : ℂ) = x :=
by rw [← exp_mul_I, abs_mul_exp_arg_mul_I]

@[simp] lemma range_exp_mul_I : range (λ x : ℝ, exp (x * I)) = metric.sphere 0 1 :=
begin
  simp only [metric.sphere, dist_eq, sub_zero],
  refine (range_subset_iff.2 $ λ x, _).antisymm (λ z (hz : abs z = 1), _),
  { exact abs_exp_of_real_mul_I _ },
  { refine ⟨arg z, _⟩,
    calc exp (arg z * I) = abs z * exp (arg z * I) : by rw [hz, of_real_one, one_mul]
    ... = z : abs_mul_exp_arg_mul_I z }
end

lemma arg_mul_cos_add_sin_mul_I {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) :
  arg (r * (cos θ + sin θ * I)) = θ :=
begin
  have hπ := real.pi_pos,
  simp only [arg, abs_mul, abs_cos_add_sin_mul_I, abs_of_nonneg hr.le, mul_one],
  simp only [of_real_mul_re, of_real_mul_im, neg_im, ← of_real_cos, ← of_real_sin,
    ← mk_eq_add_mul_I, neg_div, mul_div_cancel_left _ hr.ne',
    mul_nonneg_iff_right_nonneg_of_pos hr],
  by_cases h₁ : θ ∈ Icc (-(π / 2)) (π / 2),
  { rw if_pos, exacts [real.arcsin_sin' h₁, real.cos_nonneg_of_mem_Icc h₁] },
  { rw [mem_Icc, not_and_distrib, not_le, not_le] at h₁, cases h₁,
    { replace hθ := hθ.1,
      have hcos : real.cos θ < 0,
      { rw [← neg_pos, ← real.cos_add_pi], refine real.cos_pos_of_mem_Ioo ⟨_, _⟩; linarith },
      have hsin : real.sin θ < 0 := real.sin_neg_of_neg_of_neg_pi_lt (by linarith) hθ,
      rw [if_neg, if_neg, ← real.sin_add_pi, real.arcsin_sin, add_sub_cancel];
        [linarith, linarith, exact hsin.not_le, exact hcos.not_le] },
    { replace hθ := hθ.2,
      have hcos : real.cos θ < 0 := real.cos_neg_of_pi_div_two_lt_of_lt h₁ (by linarith),
      have hsin : 0 ≤ real.sin θ := real.sin_nonneg_of_mem_Icc ⟨by linarith, hθ⟩,
      rw [if_neg, if_pos, ← real.sin_sub_pi, real.arcsin_sin, sub_add_cancel];
        [linarith, linarith, exact hsin, exact hcos.not_le] } }
end

lemma arg_cos_add_sin_mul_I {θ : ℝ} (hθ : θ ∈ Ioc (-π) π) :
  arg (cos θ + sin θ * I) = θ :=
by rw [← one_mul (_ + _), ← of_real_one, arg_mul_cos_add_sin_mul_I zero_lt_one hθ]

@[simp] lemma arg_zero : arg 0 = 0 := by simp [arg, le_refl]

lemma ext_abs_arg {x y : ℂ} (h₁ : x.abs = y.abs) (h₂ : x.arg = y.arg) : x = y :=
by rw [← abs_mul_exp_arg_mul_I x, ← abs_mul_exp_arg_mul_I y, h₁, h₂]

lemma ext_abs_arg_iff {x y : ℂ} : x = y ↔ abs x = abs y ∧ arg x = arg y :=
⟨λ h, h ▸ ⟨rfl, rfl⟩, and_imp.2 ext_abs_arg⟩

lemma arg_mem_Ioc (z : ℂ) : arg z ∈ Ioc (-π) π :=
begin
  have hπ : 0 < π := real.pi_pos,
  rcases eq_or_ne z 0 with (rfl|hz), simp [hπ, hπ.le],
  rcases exists_unique_add_zsmul_mem_Ioc real.two_pi_pos (arg z) (-π) with ⟨N, hN, -⟩,
  rw [two_mul, neg_add_cancel_left, ← two_mul, zsmul_eq_mul] at hN,
  rw [← abs_mul_cos_add_sin_mul_I z, ← cos_add_int_mul_two_pi _ N,
    ← sin_add_int_mul_two_pi _ N],
  simp only [← of_real_one, ← of_real_bit0, ← of_real_mul, ← of_real_add, ← of_real_int_cast],
  rwa [arg_mul_cos_add_sin_mul_I (abs_pos.2 hz) hN]
end

@[simp] lemma range_arg : range arg = Ioc (-π) π :=
(range_subset_iff.2 arg_mem_Ioc).antisymm (λ x hx, ⟨_, arg_cos_add_sin_mul_I hx⟩)

lemma arg_le_pi (x : ℂ) : arg x ≤ π :=
(arg_mem_Ioc x).2

lemma neg_pi_lt_arg (x : ℂ) : -π < arg x :=
(arg_mem_Ioc x).1

@[simp] lemma arg_nonneg_iff {z : ℂ} : 0 ≤ arg z ↔ 0 ≤ z.im :=
begin
  rcases eq_or_ne z 0 with (rfl|h₀), { simp },
  calc 0 ≤ arg z ↔ 0 ≤ real.sin (arg z) :
    ⟨λ h, real.sin_nonneg_of_mem_Icc ⟨h, arg_le_pi z⟩,
      by { contrapose!, intro h, exact real.sin_neg_of_neg_of_neg_pi_lt h (neg_pi_lt_arg _) }⟩
  ... ↔ _ : by rw [sin_arg, le_div_iff (abs_pos.2 h₀), zero_mul]
end

@[simp] lemma arg_neg_iff {z : ℂ} : arg z < 0 ↔ z.im < 0 :=
lt_iff_lt_of_le_iff_le arg_nonneg_iff

lemma arg_real_mul (x : ℂ) {r : ℝ} (hr : 0 < r) : arg (r * x) = arg x :=
begin
  rcases eq_or_ne x 0 with (rfl|hx), { rw mul_zero },
  conv_lhs { rw [← abs_mul_cos_add_sin_mul_I x, ← mul_assoc, ← of_real_mul,
    arg_mul_cos_add_sin_mul_I (mul_pos hr (abs_pos.2 hx)) x.arg_mem_Ioc] }
end

lemma arg_eq_arg_iff {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
  arg x = arg y ↔ (abs y / abs x : ℂ) * x = y :=
begin
  simp only [ext_abs_arg_iff, abs_mul, abs_div, abs_of_real, abs_abs,
    div_mul_cancel _ (abs_ne_zero.2 hx), eq_self_iff_true, true_and],
  rw [← of_real_div, arg_real_mul],
  exact div_pos (abs_pos.2 hy) (abs_pos.2 hx)
end

@[simp] lemma arg_one : arg 1 = 0 :=
by simp [arg, zero_le_one]

@[simp] lemma arg_neg_one : arg (-1) = π :=
by simp [arg, le_refl, not_le.2 (@zero_lt_one ℝ _ _)]

@[simp] lemma arg_I : arg I = π / 2 :=
by simp [arg, le_refl]

@[simp] lemma arg_neg_I : arg (-I) = -(π / 2) :=
by simp [arg, le_refl]

@[simp] lemma tan_arg (x : ℂ) : real.tan (arg x) = x.im / x.re :=
begin
  by_cases h : x = 0,
  { simp only [h, zero_div, complex.zero_im, complex.arg_zero, real.tan_zero, complex.zero_re] },
  rw [real.tan_eq_sin_div_cos, sin_arg, cos_arg h,
      div_div_div_cancel_right _ (abs_ne_zero.2 h)]
end

lemma arg_of_real_of_nonneg {x : ℝ} (hx : 0 ≤ x) : arg x = 0 :=
by simp [arg, hx]

lemma arg_eq_pi_iff {z : ℂ} : arg z = π ↔ z.re < 0 ∧ z.im = 0 :=
begin
  by_cases h₀ : z = 0, { simp [h₀, lt_irrefl, real.pi_ne_zero.symm] },
  split,
  { intro h, rw [← abs_mul_cos_add_sin_mul_I z, h], simp [h₀] },
  { cases z with x y, rintro ⟨h : x < 0, rfl : y = 0⟩,
    rw [← arg_neg_one, ← arg_real_mul (-1) (neg_pos.2 h)], simp [← of_real_def] }
end

lemma arg_of_real_of_neg {x : ℝ} (hx : x < 0) : arg x = π :=
arg_eq_pi_iff.2 ⟨hx, rfl⟩

lemma arg_eq_pi_div_two_iff {z : ℂ} : arg z = π / 2 ↔ z.re = 0 ∧ 0 < z.im :=
begin
  by_cases h₀ : z = 0, { simp [h₀, lt_irrefl, real.pi_div_two_pos.ne] },
  split,
  { intro h, rw [← abs_mul_cos_add_sin_mul_I z, h], simp [h₀] },
  { cases z with x y, rintro ⟨rfl : x = 0, hy : 0 < y⟩,
    rw [← arg_I, ← arg_real_mul I hy, of_real_mul', I_re, I_im, mul_zero, mul_one] }
end

lemma arg_eq_neg_pi_div_two_iff {z : ℂ} : arg z = - (π / 2) ↔ z.re = 0 ∧ z.im < 0 :=
begin
  by_cases h₀ : z = 0, { simp [h₀, lt_irrefl, real.pi_ne_zero] },
  split,
  { intro h, rw [← abs_mul_cos_add_sin_mul_I z, h], simp [h₀] },
  { cases z with x y, rintro ⟨rfl : x = 0, hy : y < 0⟩,
    rw [← arg_neg_I, ← arg_real_mul (-I) (neg_pos.2 hy), mk_eq_add_mul_I],
    simp }
end

lemma arg_of_re_nonneg {x : ℂ} (hx : 0 ≤ x.re) : arg x = real.arcsin (x.im / x.abs) :=
if_pos hx

lemma arg_of_re_neg_of_im_nonneg {x : ℂ} (hx_re : x.re < 0) (hx_im : 0 ≤ x.im) :
  arg x = real.arcsin ((-x).im / x.abs) + π :=
by simp only [arg, hx_re.not_le, hx_im, if_true, if_false]

lemma arg_of_re_neg_of_im_neg {x : ℂ} (hx_re : x.re < 0) (hx_im : x.im < 0) :
  arg x = real.arcsin ((-x).im / x.abs) - π :=
by simp only [arg, hx_re.not_le, hx_im.not_le, if_false]

lemma arg_of_im_nonneg_of_ne_zero {z : ℂ} (h₁ : 0 ≤ z.im) (h₂ : z ≠ 0) :
  arg z = real.arccos (z.re / abs z) :=
by rw [← cos_arg h₂, real.arccos_cos (arg_nonneg_iff.2 h₁) (arg_le_pi _)]

lemma arg_of_im_pos {z : ℂ} (hz : 0 < z.im) : arg z = real.arccos (z.re / abs z) :=
arg_of_im_nonneg_of_ne_zero hz.le (λ h, hz.ne' $ h.symm ▸ rfl)

lemma arg_of_im_neg {z : ℂ} (hz : z.im < 0) : arg z = -real.arccos (z.re / abs z) :=
begin
  have h₀ : z ≠ 0, from mt (congr_arg im) hz.ne,
  rw [← cos_arg h₀, ← real.cos_neg, real.arccos_cos, neg_neg],
  exacts [neg_nonneg.2 (arg_neg_iff.2 hz).le, neg_le.2 (neg_pi_lt_arg z).le]
end

lemma arg_conj (x : ℂ) : arg (conj x) = if arg x = π then π else -arg x :=
begin
  simp_rw [arg_eq_pi_iff, arg, neg_im, conj_im, conj_re, abs_conj, neg_div, neg_neg,
           real.arcsin_neg, apply_ite has_neg.neg, neg_add, neg_sub, neg_neg, ←sub_eq_add_neg,
           sub_neg_eq_add, add_comm π],
  rcases lt_trichotomy x.re 0 with (hr|hr|hr); rcases lt_trichotomy x.im 0 with (hi|hi|hi),
  { simp [hr, hr.not_le, hi.le, hi.ne, not_le.2 hi] },
  { simp [hr, hr.not_le, hi] },
  { simp [hr, hr.not_le, hi.ne.symm, hi.le, not_le.2 hi] },
  { simp [hr] },
  { simp [hr] },
  { simp [hr] },
  { simp [hr, hr.le, hi.ne] },
  { simp [hr, hr.le, hr.le.not_lt] },
  { simp [hr, hr.le, hr.le.not_lt] },
end

lemma arg_inv (x : ℂ) : arg x⁻¹ = if arg x = π then π else -arg x :=
begin
  rw [←arg_conj, inv_def, mul_comm],
  by_cases hx : x = 0,
  { simp [hx] },
  { exact arg_real_mul (conj x) (by simp [hx]) }
end

@[simp] lemma arg_conj_coe_angle (x : ℂ) : (arg (conj x) : real.angle) = -arg x :=
begin
  by_cases h : arg x = π;
    simp [arg_conj, h]
end

@[simp] lemma arg_inv_coe_angle (x : ℂ) : (arg x⁻¹ : real.angle) = -arg x :=
begin
  by_cases h : arg x = π;
    simp [arg_inv, h]
end

lemma arg_neg_eq_arg_sub_pi_of_im_pos {x : ℂ} (hi : 0 < x.im) : arg (-x) = arg x - π :=
begin
  rw [arg_of_im_pos hi, arg_of_im_neg (show (-x).im < 0, from left.neg_neg_iff.2 hi)],
  simp [neg_div, real.arccos_neg]
end

lemma arg_neg_eq_arg_add_pi_of_im_neg {x : ℂ} (hi : x.im < 0) : arg (-x) = arg x + π :=
begin
  rw [arg_of_im_neg hi, arg_of_im_pos (show 0 < (-x).im, from left.neg_pos_iff.2 hi)],
  simp [neg_div, real.arccos_neg, add_comm, ←sub_eq_add_neg]
end

lemma arg_neg_eq_arg_sub_pi_iff {x : ℂ} :
  arg (-x) = arg x - π ↔ (0 < x.im ∨ x.im = 0 ∧ x.re < 0) :=
begin
  rcases lt_trichotomy x.im 0 with (hi|hi|hi),
  { simp [hi, hi.ne, hi.not_lt, arg_neg_eq_arg_add_pi_of_im_neg, sub_eq_add_neg,
          ←add_eq_zero_iff_eq_neg, real.pi_ne_zero] },
  { rw (ext rfl hi : x = x.re),
    rcases lt_trichotomy x.re 0 with (hr|hr|hr),
    { rw [arg_of_real_of_neg hr, ←of_real_neg, arg_of_real_of_nonneg (left.neg_pos_iff.2 hr).le],
      simp [hr] },
    { simp [hr, hi, real.pi_ne_zero] },
    { rw [arg_of_real_of_nonneg hr.le, ←of_real_neg, arg_of_real_of_neg (left.neg_neg_iff.2 hr)],
      simp [hr.not_lt, ←add_eq_zero_iff_eq_neg, real.pi_ne_zero] } },
  { simp [hi, arg_neg_eq_arg_sub_pi_of_im_pos] }
end

lemma arg_neg_eq_arg_add_pi_iff {x : ℂ} :
  arg (-x) = arg x + π ↔ (x.im < 0 ∨ x.im = 0 ∧ 0 < x.re) :=
begin
  rcases lt_trichotomy x.im 0 with (hi|hi|hi),
  { simp [hi, arg_neg_eq_arg_add_pi_of_im_neg] },
  { rw (ext rfl hi : x = x.re),
    rcases lt_trichotomy x.re 0 with (hr|hr|hr),
    { rw [arg_of_real_of_neg hr, ←of_real_neg, arg_of_real_of_nonneg (left.neg_pos_iff.2 hr).le],
      simp [hr.not_lt, ←two_mul, real.pi_ne_zero] },
    { simp [hr, hi, real.pi_ne_zero.symm] },
    { rw [arg_of_real_of_nonneg hr.le, ←of_real_neg, arg_of_real_of_neg (left.neg_neg_iff.2 hr)],
      simp [hr] } },
  { simp [hi, hi.ne.symm, hi.not_lt, arg_neg_eq_arg_sub_pi_of_im_pos, sub_eq_add_neg,
          ←add_eq_zero_iff_neg_eq, real.pi_ne_zero] }
end

lemma arg_neg_coe_angle {x : ℂ} (hx : x ≠ 0) : (arg (-x) : real.angle) = arg x + π :=
begin
  rcases lt_trichotomy x.im 0 with (hi|hi|hi),
  { rw [arg_neg_eq_arg_add_pi_of_im_neg hi, real.angle.coe_add] },
  { rw (ext rfl hi : x = x.re),
    rcases lt_trichotomy x.re 0 with (hr|hr|hr),
    { rw [arg_of_real_of_neg hr, ←of_real_neg, arg_of_real_of_nonneg (left.neg_pos_iff.2 hr).le,
          ←real.angle.coe_add, ←two_mul, real.angle.coe_two_pi, real.angle.coe_zero] },
    { exact false.elim (hx (ext hr hi)) },
    { rw [arg_of_real_of_nonneg hr.le, ←of_real_neg, arg_of_real_of_neg (left.neg_neg_iff.2 hr),
          real.angle.coe_zero, zero_add] } },
  { rw [arg_neg_eq_arg_sub_pi_of_im_pos hi, real.angle.coe_sub,
        real.angle.sub_coe_pi_eq_add_coe_pi] }
end

lemma arg_mul_cos_add_sin_mul_I_eq_mul_fract {r : ℝ} (hr : 0 < r) (θ : ℝ) :
  arg (r * (cos θ + sin θ * I)) = π - 2 * π * int.fract ((π - θ) / (2 * π)) :=
begin
  have hi : π - 2 * π * int.fract ((π - θ) / (2 * π)) ∈ Ioc (-π) π,
  { rw [←mem_preimage, preimage_const_sub_Ioc, ←mem_preimage,
        preimage_const_mul_Ico _ _ real.two_pi_pos, sub_self, zero_div, sub_neg_eq_add,
        ←two_mul, div_self real.two_pi_pos.ne.symm],
    refine set.mem_of_mem_of_subset (set.mem_range_self _) _,
    rw [←image_univ, int.image_fract],
    simp },
  have hs : π - 2 * π * int.fract ((π - θ) / (2 * π)) = 2 * π * ⌊(π - θ) / (2 * π)⌋ + θ,
  { rw [int.fract, mul_sub, mul_div_cancel' _ real.two_pi_pos.ne.symm],
    abel },
  convert arg_mul_cos_add_sin_mul_I hr hi using 3,
  simp_rw [hs, mul_comm (2 * π), add_comm _ θ, ←of_real_cos, ←of_real_sin,
           real.cos_add_int_mul_two_pi, real.sin_add_int_mul_two_pi]
end

lemma arg_cos_add_sin_mul_I_eq_mul_fract (θ : ℝ) :
  arg (cos θ + sin θ * I) = π - 2 * π * int.fract ((π - θ) / (2 * π)) :=
by rw [←one_mul (_ + _), ←of_real_one, arg_mul_cos_add_sin_mul_I_eq_mul_fract zero_lt_one]

lemma arg_mul_cos_add_sin_mul_I_sub {r : ℝ} (hr : 0 < r) (θ : ℝ) :
  arg (r * (cos θ + sin θ * I)) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ :=
begin
  rw [arg_mul_cos_add_sin_mul_I_eq_mul_fract hr, int.fract, mul_sub,
      mul_div_cancel' _ real.two_pi_pos.ne.symm],
  abel
end

lemma arg_cos_add_sin_mul_I_sub (θ : ℝ) :
  arg (cos θ + sin θ * I) - θ = 2 * π * ⌊(π - θ) / (2 * π)⌋ :=
by rw [←one_mul (_ + _), ←of_real_one, arg_mul_cos_add_sin_mul_I_sub zero_lt_one]

lemma arg_mul_cos_add_sin_mul_I_coe_angle {r : ℝ} (hr : 0 < r) (θ : real.angle) :
  (arg (r * (real.angle.cos θ + real.angle.sin θ * I)) : real.angle) = θ :=
begin
  induction θ using real.angle.induction_on,
  rw [real.angle.cos_coe, real.angle.sin_coe, real.angle.angle_eq_iff_two_pi_dvd_sub],
  use ⌊(π - θ) / (2 * π)⌋,
  exact_mod_cast arg_mul_cos_add_sin_mul_I_sub hr θ
end

lemma arg_cos_add_sin_mul_I_coe_angle (θ : real.angle) :
  (arg (real.angle.cos θ + real.angle.sin θ * I) : real.angle) = θ :=
by rw [←one_mul (_ + _), ←of_real_one, arg_mul_cos_add_sin_mul_I_coe_angle zero_lt_one]

lemma arg_mul_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
  (arg (x * y) : real.angle) = arg x + arg y :=
begin
  convert arg_mul_cos_add_sin_mul_I_coe_angle (mul_pos (abs_pos.2 hx) (abs_pos.2 hy))
                                              (arg x + arg y : real.angle) using 3,
  simp_rw [←real.angle.coe_add, real.angle.sin_coe, real.angle.cos_coe, of_real_cos,
           of_real_sin, cos_add_sin_I, of_real_add, add_mul, exp_add, of_real_mul],
  rw [mul_assoc, mul_comm (exp _), ←mul_assoc (abs y : ℂ), abs_mul_exp_arg_mul_I, mul_comm y,
      ←mul_assoc, abs_mul_exp_arg_mul_I]
end

lemma arg_div_coe_angle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
  (arg (x / y) : real.angle) = arg x - arg y :=
by rw [div_eq_mul_inv, arg_mul_coe_angle hx (inv_ne_zero hy), arg_inv_coe_angle, sub_eq_add_neg]

@[simp] lemma arg_coe_angle_eq_iff {x y : ℂ} : (arg x : real.angle) = arg y ↔ arg x = arg y :=
begin
  split,
  { intro h,
    rw real.angle.angle_eq_iff_two_pi_dvd_sub at h,
    rcases h with ⟨k, hk⟩,
    rw ←sub_eq_zero,
    have ha : -(2 * π) < arg x - arg y,
    { linarith only [neg_pi_lt_arg x, arg_le_pi y] },
    have hb : arg x - arg y < 2 * π,
    { linarith only [arg_le_pi x, neg_pi_lt_arg y] },
    rw [hk, neg_lt, neg_mul_eq_mul_neg, mul_lt_iff_lt_one_right real.two_pi_pos, neg_lt,
        ←int.cast_one, ←int.cast_neg, int.cast_lt] at ha,
    rw [hk, mul_lt_iff_lt_one_right real.two_pi_pos, ←int.cast_one, int.cast_lt] at hb,
    have hk' : k = 0,
    { linarith only [ha, hb] },
    rw hk' at hk,
    simpa using hk },
  { intro h,
    rw h }
end

section continuity

variables {x z : ℂ}

lemma arg_eq_nhds_of_re_pos (hx : 0 < x.re) : arg =ᶠ[𝓝 x] λ x, real.arcsin (x.im / x.abs) :=
((continuous_re.tendsto _).eventually (lt_mem_nhds hx)).mono $ λ y hy, arg_of_re_nonneg hy.le

lemma arg_eq_nhds_of_re_neg_of_im_pos (hx_re : x.re < 0) (hx_im : 0 < x.im) :
  arg =ᶠ[𝓝 x] λ x, real.arcsin ((-x).im / x.abs) + π :=
begin
  suffices h_forall_nhds : ∀ᶠ (y : ℂ) in (𝓝 x), y.re < 0 ∧ 0 < y.im,
    from h_forall_nhds.mono (λ y hy, arg_of_re_neg_of_im_nonneg hy.1 hy.2.le),
  refine is_open.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ 0 < x.im),
  exact is_open.and (is_open_lt continuous_re continuous_zero)
    (is_open_lt continuous_zero continuous_im),
end

lemma arg_eq_nhds_of_re_neg_of_im_neg (hx_re : x.re < 0) (hx_im : x.im < 0) :
  arg =ᶠ[𝓝 x] λ x, real.arcsin ((-x).im / x.abs) - π :=
begin
  suffices h_forall_nhds : ∀ᶠ (y : ℂ) in (𝓝 x), y.re < 0 ∧ y.im < 0,
    from h_forall_nhds.mono (λ y hy, arg_of_re_neg_of_im_neg hy.1 hy.2),
  refine is_open.eventually_mem _ (⟨hx_re, hx_im⟩ : x.re < 0 ∧ x.im < 0),
  exact is_open.and (is_open_lt continuous_re continuous_zero)
    (is_open_lt continuous_im continuous_zero),
end

lemma arg_eq_nhds_of_im_pos (hz : 0 < im z) :
  arg =ᶠ[𝓝 z] λ x, real.arccos (x.re / abs x) :=
((continuous_im.tendsto _).eventually (lt_mem_nhds hz)).mono $ λ x, arg_of_im_pos

lemma arg_eq_nhds_of_im_neg (hz : im z < 0) :
  arg =ᶠ[𝓝 z] λ x, -real.arccos (x.re / abs x) :=
((continuous_im.tendsto _).eventually (gt_mem_nhds hz)).mono $ λ x, arg_of_im_neg

lemma continuous_at_arg (h : 0 < x.re ∨ x.im ≠ 0) : continuous_at arg x :=
begin
  have h₀ : abs x ≠ 0, { rw abs_ne_zero, rintro rfl, simpa using h },
  rw [← lt_or_lt_iff_ne] at h,
  rcases h with (hx_re|hx_im|hx_im),
  exacts [(real.continuous_at_arcsin.comp (continuous_im.continuous_at.div
    continuous_abs.continuous_at h₀)).congr (arg_eq_nhds_of_re_pos hx_re).symm,
    (real.continuous_arccos.continuous_at.comp (continuous_re.continuous_at.div
      continuous_abs.continuous_at h₀)).neg.congr (arg_eq_nhds_of_im_neg hx_im).symm,
    (real.continuous_arccos.continuous_at.comp (continuous_re.continuous_at.div
      continuous_abs.continuous_at h₀)).congr (arg_eq_nhds_of_im_pos hx_im).symm]
end

lemma tendsto_arg_nhds_within_im_neg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto arg (𝓝[{z : ℂ | z.im < 0}] z) (𝓝 (-π)) :=
begin
  suffices H :
    tendsto (λ x : ℂ, real.arcsin ((-x).im / x.abs) - π) (𝓝[{z : ℂ | z.im < 0}] z) (𝓝 (-π)),
  { refine H.congr' _,
    have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0, from continuous_re.tendsto z (gt_mem_nhds hre),
    filter_upwards [self_mem_nhds_within, mem_nhds_within_of_mem_nhds this] with _ him hre,
    rw [arg, if_neg hre.not_le, if_neg him.not_le], },
  convert (real.continuous_at_arcsin.comp_continuous_within_at
    ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div
      continuous_abs.continuous_within_at _)).sub tendsto_const_nhds,
  { simp [him] },
  { lift z to ℝ using him, simpa using hre.ne }
end

lemma continuous_within_at_arg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  continuous_within_at arg {z : ℂ | 0 ≤ z.im} z :=
begin
  have : arg =ᶠ[𝓝[{z : ℂ | 0 ≤ z.im}] z] λ x, real.arcsin ((-x).im / x.abs) + π,
  { have : ∀ᶠ x : ℂ in 𝓝 z, x.re < 0, from continuous_re.tendsto z (gt_mem_nhds hre),
    filter_upwards [self_mem_nhds_within, mem_nhds_within_of_mem_nhds this] with _ him hre,
    rw [arg, if_neg hre.not_le, if_pos him] },
  refine continuous_within_at.congr_of_eventually_eq _ this _,
  { refine (real.continuous_at_arcsin.comp_continuous_within_at
      ((continuous_im.continuous_at.comp_continuous_within_at continuous_within_at_neg).div
        continuous_abs.continuous_within_at _)).add tendsto_const_nhds,
    lift z to ℝ using him, simpa using hre.ne },
  { rw [arg, if_neg hre.not_le, if_pos him.ge] }
end

lemma tendsto_arg_nhds_within_im_nonneg_of_re_neg_of_im_zero
  {z : ℂ} (hre : z.re < 0) (him : z.im = 0) :
  tendsto arg (𝓝[{z : ℂ | 0 ≤ z.im}] z) (𝓝 π) :=
by simpa only [arg_eq_pi_iff.2 ⟨hre, him⟩]
  using (continuous_within_at_arg_of_re_neg_of_im_zero hre him).tendsto

end continuity

end complex
