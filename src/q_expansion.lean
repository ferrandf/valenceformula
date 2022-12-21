import .mod_f
import .holomorphic_functions
import analysis.complex.removable_singularity
import analysis.complex.upper_half_plane.basic
import analysis.complex.upper_half_plane.topology
import number_theory.modular
import group_theory.index
import .upper_half_plane_manifold

/-!
# The original file can be found in https://github.com/CBirkbeck/ModularForms/blob/2d45f5501a0390c2150a6882f1dc6e07f3589847/src/mod_forms/q_expansion.lean
# By Chris Birkbeck
# q-expansions of periodic functions (Modified by Ferran Delgà)
We show that if `f : ℂ → ℂ` satisfies `f(z + h) = f(z)`, for some nonzero real `h`, then
there is a well-defined `F` such that `f(z) = F(exp(2 * π * I * z / h))` for all `z`;
and if `f` is holomorphic at some `z`, then `F` is holomorphic at `q = exp (2 * π * I * z / h)`.
We also show (using Riemann's removable singularity theorem) that if `f` is holomorphic and bounded
for all sufficiently large `im z`, then `F` extends to a holomorphic function on a neighbourhood of
`0`. As a consequence, if `f` tends to zero as `im z → ∞`, then in fact it decays *exponentially*
to zero.
-/

open modular_form complex filter asymptotics
open_locale real topological_space manifold filter

noncomputable theory

abbreviation ℝ_pos := {u : ℝ // 0 < u}

instance : has_one ℝ_pos := by { use 1, }

/-- Function-theoretic lemma, maybe move this elsewhere? -/
lemma bound_holo_fcn (g : ℂ → ℂ) (hg : differentiable_at ℂ g 0) (hg' : g 0 = 0):
  is_O (𝓝 0) g id  :=
begin
  replace hg := hg.has_deriv_at.is_O_sub, simp_rw [hg', sub_zero] at hg, exact hg,
end


section Q_and_Z

variables (h : ℝ_pos)

def Q (z : ℂ) : ℂ := exp ( 2 * π * I * z / h )

def Z (q : ℂ) : ℂ := h / (2 * π * I) * log q

lemma log_exp' (z : ℂ) : ∃ (n : ℤ), log (exp z) = z + n * (2 * π * I) :=
begin
  rw [←exp_eq_exp_iff_exists_int, exp_log], exact exp_ne_zero z,
end

lemma QZ_eq_id (q : ℂ) (hq : q ≠ 0) : Q h (Z h q) = q :=
begin
  dsimp only [Q, Z],
  suffices : 2 * ↑π * I * (↑h / (2 * ↑π * I) * log q) / ↑h = log q,
  { rw this, exact exp_log hq },
  have : (h : ℂ) ≠ 0 := of_real_ne_zero.mpr h.2.ne',
  field_simp [two_pi_I_ne_zero, this], ring,
end

lemma abs_Q_eq (z : ℂ) : abs (Q h z) = real.exp(-2 * π * im z / h) :=
begin
  dsimp only [Q], rw abs_exp, congr,
  rw [div_eq_mul_inv, mul_comm],
  have : (↑h)⁻¹ = (↑((h : ℝ)⁻¹) : ℂ) := by simp, rw this,
  rw of_real_mul_re,
  have : 2 * ↑π * I * z = (↑(2 * π) * z) * I := by { simp, ring, },
  rw [this, mul_I_re, of_real_mul_im], field_simp [h.2.ne'],
end

lemma im_Z_eq (q : ℂ) (hq : q ≠ 0) : im (Z h q) = -h / (2 * π) * real.log (abs q) :=
begin
  dsimp only [Z],
  have : ↑h / (2 * ↑π * I) * log q = -↑h / (2 * ↑π) * log q * I,
  { field_simp [of_real_ne_zero.mpr real.pi_pos.ne', two_pi_I_ne_zero], ring_nf, simp, },
  rw [this, mul_I_im],
  have : -↑h / (2 * ↑π) * log q = ↑(-↑h / (2 * π)) * log q := by simp,
  rw [this, of_real_mul_re, log_re],
end

lemma ZQ_eq_mod_period (z : ℂ) : ∃ (m : ℤ), Z h (Q h z) = z + m * h :=
begin
  dsimp only [Q, Z],
  have t := log_exp' ( 2 * ↑π * I * z / ↑h ),
  cases t with m t, use m, rw t,
  have : (h:ℂ) ≠ 0 := of_real_ne_zero.mpr h.2.ne',
  field_simp [two_pi_I_ne_zero], ring,
end

lemma abs_q_lt_iff (A : ℝ) (z : ℂ) : abs (Q h z) < real.exp(-2 * π * A / h) ↔ A < im z :=
begin
  rw [abs_Q_eq, real.exp_lt_exp],
  split,
  { intro hz, rw div_lt_div_right at hz, swap, exact h.2,
    have : (-2) * π < 0 := by simpa using real.pi_pos,
    rwa mul_lt_mul_left_of_neg this at hz, },
  { intro hz, rw div_lt_div_right, swap, exact h.2,
    have : (-2) * π < 0 := by simpa using real.pi_pos,
    rwa mul_lt_mul_left_of_neg this, },
end

-- Filter stuff

def at_I_inf' : filter ℂ := at_top.comap im

lemma at_I_inf'_mem (S : set ℂ) : S ∈ at_I_inf' ↔ (∃ A : ℝ, ∀ z : ℂ, A < im z → z ∈ S) :=
begin
  rw [at_I_inf', mem_comap', mem_at_top_sets],
  simp, split,
  { intro h, cases h with a h, use a,
    intros z hz, specialize h (im z) hz.le, apply h, refl },
  { intro h, cases h with A h, use A + 1,
    intros b hb x hx, apply (h x), rw hx, linarith, }
end

lemma Z_tendsto : tendsto (Z h) (𝓝[{0}ᶜ] 0) at_I_inf' :=
begin
  rw [tendsto, map_le_iff_le_comap, comap],
  intros S h, simp_rw at_I_inf'_mem at h, obtain ⟨T, ⟨A, hA⟩, hT⟩ := h,
  simp_rw [metric.mem_nhds_within_iff, metric.ball, dist_eq, sub_zero],
  use real.exp(-2 * π * A / h), split, apply real.exp_pos,
  intro q, dsimp, rintro ⟨u1, u2⟩,
  rw [←(QZ_eq_id h _ u2), abs_q_lt_iff] at u1, specialize hA (Z h q) u1,
  apply hT, exact hA,
end

lemma Q_tendsto : tendsto (Q h) at_I_inf' (𝓝 0) :=
begin
  rw [tendsto_zero_iff_norm_tendsto_zero],
  simp_rw [norm_eq_abs,abs_Q_eq],
  have : set.range im ∈ at_top,
  { suffices : set.range im = ⊤, { rw this, apply univ_mem, },
    ext1, simp only [set.mem_range, set.top_eq_univ, set.mem_univ, iff_true],
    use I * x, simp, },
  have := (@tendsto_comap'_iff ℝ ℝ ℂ (λ y, real.exp ((-2) * π * y / ↑h)) at_top (𝓝 0) im this).mpr,
  apply this, refine real.tendsto_exp_at_bot.comp _,
  apply tendsto.at_bot_div_const h.2,
  apply tendsto.neg_const_mul_at_top, { simpa using real.pi_pos }, exact tendsto_id,
end

end Q_and_Z

section periodic_on_C

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))

def cusp_fcn_0 : ℂ → ℂ := λ q, f (Z h q)

def cusp_fcn : ℂ → ℂ := function.update (cusp_fcn_0 h f) 0 (lim (𝓝[≠] (0:ℂ)) (cusp_fcn_0 h f))

lemma cusp_fcn_eq_of_nonzero (q : ℂ) (hq : q ≠ 0) :
  (cusp_fcn h f) q = (cusp_fcn_0 h f) q :=
begin
  rw [cusp_fcn, function.update], split_ifs,
  { exfalso, exact hq h_1 },
  { refl },
end

lemma update_twice :
  cusp_fcn h f = function.update (cusp_fcn h f) 0 (lim (𝓝[≠] (0:ℂ)) (cusp_fcn h f)) :=
begin
  ext1 q, rw function.update, split_ifs,
  { rw [cusp_fcn, function.update], split_ifs,
    congr' 1, rw [lim, lim], congr' 1,
    apply map_congr, apply eventually_eq_nhds_within_of_eq_on,
    intros r hr, simp at hr,
    rw function.update, split_ifs, refl,},
  { refl, },
end

include hf

private lemma is_periodic_aux (z : ℂ) (m : ℕ) : f (z + m * h) = f z :=
begin
  induction m with m hm generalizing z, simp,
  rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one, add_mul, ←add_assoc, one_mul],
  rw hf (z + m * h), exact hm z,
end

lemma is_periodic (z : ℂ) (m : ℤ) : f (z + m * h) = f z :=
begin
  cases m, { exact is_periodic_aux h f hf z m },
  simp only [neg_add_rev, int.cast_neg_succ_of_nat],
  convert (is_periodic_aux h f hf (z - (m+1) * h) (m+1)).symm,
  { simp, ring }, { simp },
end

lemma eq_cusp_fcn (z : ℂ) : f z = (cusp_fcn h f) (Q h z) :=
begin
  have : (cusp_fcn h f) (Q h z) = (cusp_fcn_0 h f) (Q h z),
  { rw cusp_fcn, rw function.update, split_ifs,
    { exfalso, have : Q h z ≠ 0 := by apply exp_ne_zero, exact this h_1, },
    { refl } },
  rw this,
  dsimp only [cusp_fcn_0],
  obtain ⟨m, hm⟩ := ZQ_eq_mod_period h z,
  rw hm, exact (is_periodic h f hf z m).symm,
end

end periodic_on_C

section holo_on_C

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))
include hf

lemma cusp_fcn_diff_at (z : ℂ) (hol_z : differentiable_at ℂ f z) :
  differentiable_at ℂ (cusp_fcn h f) (Q h z) :=
begin
  let q := Q h z,
  have qdiff : has_strict_deriv_at (Q h) (q * (2 * π * I / h)) z,
  { apply has_strict_deriv_at.cexp,
    apply has_strict_deriv_at.div_const,
    have : 2 * ↑π * I = (2 * ↑π * I) * 1 := by ring,
    conv begin congr, skip, rw this, end,
    exact has_strict_deriv_at.const_mul _ (has_strict_deriv_at_id _) },
  -- Now show that the q-map has a differentiable local inverse at z, say L : ℂ → ℂ, with L(q) = z.
  have diff_ne : (q * (2 * π * I / h)) ≠ 0,
  { apply mul_ne_zero, apply exp_ne_zero, apply div_ne_zero,
    exact two_pi_I_ne_zero, simpa using h.2.ne', },
  let L := (qdiff.local_inverse (Q h) _ z) diff_ne,
  have diff_L : differentiable_at ℂ L q := (qdiff.to_local_inverse diff_ne).differentiable_at,
  have hL : (Q h) ∘ L =ᶠ[𝓝 q] (id : ℂ → ℂ),
  { exact (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_right_inverse },
  --Thus, if F = cusp_expansion f, we have F(q') = f(L(q')) for q' near q.
  --Since L is differentiable at q, and f is diffble at L(q) [ = z], we conclude
  --that F is differentiable at q.
  have hF := eventually_eq.fun_comp hL (cusp_fcn h f), dsimp at hF,
  have : (cusp_fcn h f) ∘ (Q h) ∘ L = f ∘ L := by { ext1 z, exact (eq_cusp_fcn h f hf (L z)).symm },
  rw this at hF,
  have : z = L(q),
  { have hL2 : (L ∘ (Q h)) =ᶠ[𝓝 z] (id : ℂ → ℂ),
    { exact (qdiff.has_strict_fderiv_at_equiv diff_ne).eventually_left_inverse },
    replace hL2 := eventually_eq.eq_of_nhds hL2, dsimp at hL2, rw hL2, },
  rw this at hol_z,
  exact (differentiable_at.comp q hol_z diff_L).congr_of_eventually_eq hF.symm,
end

lemma F_diff_near_zero (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  ∀ᶠ (q : ℂ) in 𝓝[≠] 0, differentiable_at ℂ (cusp_fcn h f) q :=
begin
  refine ((Z_tendsto h).eventually h_hol).mp _,
  apply eventually_nhds_within_of_forall, intros q hq h_diff,
  rw ←(QZ_eq_id _ _ hq), exact cusp_fcn_diff_at _ _ hf _ h_diff,
end

end holo_on_C

section holo_at_inf_C

variables (h : ℝ_pos) (f : ℂ → ℂ) (hf : ∀ (w : ℂ), f(w + h) = f(w))
include hf

lemma F_bound (h_bd : is_O at_I_inf' f (1 : ℂ → ℂ) ) : is_O (𝓝[≠] (0 : ℂ)) (cusp_fcn h f) (1 : ℂ → ℂ)  :=
begin
  refine is_O.congr' (h_bd.comp_tendsto $ Z_tendsto h) _ (by refl) ,
  apply eventually_nhds_within_of_forall, intros q hq,
  rw cusp_fcn_eq_of_nonzero _ _ _ hq, refl,
end

set_option trace.simp_lemmas true

lemma F_diff_at_zero (h_bd : is_O at_I_inf' f (1 : ℂ → ℂ) )
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  differentiable_at ℂ (cusp_fcn h f) 0 :=
begin
  obtain ⟨c, t⟩ := (F_bound _ _ hf h_bd).bound,
  replace t := (F_diff_near_zero h f hf h_hol).and t,
  simp only [norm_eq_abs, pi.one_apply, absolute_value.map_one, mul_one] at t,
  obtain ⟨S, hS1, hS2, hS3⟩ := eventually_nhds_iff.mp (eventually_nhds_within_iff.mp t),
  have h_diff : differentiable_on ℂ (cusp_fcn h f) (S \ {0}),
  { intros x hx, apply differentiable_at.differentiable_within_at,
    exact (hS1 x ((set.mem_diff _).mp hx).1  ((set.mem_diff _).mp hx).2).1, },
  have hF_bd : bdd_above (norm ∘ (cusp_fcn h f) '' (S \ {0})),
  { use c, rw mem_upper_bounds, simp, intros y q hq hq2 hy, rw ←hy, exact (hS1 q hq hq2).2,},
  have := differentiable_on_update_lim_of_bdd_above (is_open.mem_nhds hS2 hS3) h_diff hF_bd,
  rw ←update_twice at this,
  exact this.differentiable_at (is_open.mem_nhds hS2 hS3),
end

/-- If `f` is periodic, and holomorphic and bounded near `I∞`, then it tends to a limit at `I∞`,
and this limit is the value of its cusp function at 0. -/
theorem tendsto_at_I_inf (h_bd : is_O at_I_inf' f (1 : ℂ → ℂ) )
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  tendsto f at_I_inf' (𝓝 $ cusp_fcn h f 0) :=
begin
  suffices : tendsto (cusp_fcn h f) (𝓝[≠] 0) (𝓝 $ cusp_fcn h f 0),
  { have t2 : f = (cusp_fcn h f) ∘ (Q h) := by { ext1, apply eq_cusp_fcn h f hf },
    conv begin congr, rw t2, end,
    apply tendsto.comp, exact this,
    apply tendsto_nhds_within_of_tendsto_nhds_of_eventually_within,
    exact Q_tendsto h, apply eventually_of_forall, intro q, apply exp_ne_zero, },
  exact tendsto_nhds_within_of_tendsto_nhds (F_diff_at_zero _ _ hf h_bd h_hol).continuous_at.tendsto
end

lemma cusp_fcn_zero_of_zero_at_inf (h_bd : is_o at_I_inf' f (1 : ℂ → ℂ) )
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) : cusp_fcn h f 0 = 0 :=
begin
  rw [cusp_fcn, function.update], split_ifs, swap, tauto,
  suffices : tendsto (cusp_fcn_0 h f) (𝓝[{0}ᶜ] 0) (𝓝 (0:ℂ)),
  { exact tendsto.lim_eq this },
  have : is_o (𝓝[≠] (0 : ℂ)) (cusp_fcn h f) 1 ,
  { refine is_o.congr' (h_bd.comp_tendsto $ Z_tendsto h) _ (by refl) ,
    apply eventually_nhds_within_of_forall, intros q hq, rw cusp_fcn_eq_of_nonzero _ _ _ hq, refl },
  have : is_o (𝓝[≠] (0 : ℂ)) (cusp_fcn_0 h f) 1,
  { refine is_o.congr' this _ (by refl), apply eventually_nhds_within_of_forall,
    apply cusp_fcn_eq_of_nonzero, },
  simpa using this.tendsto_div_nhds_zero,
end

/-- Main theorem of this file: if `f` is periodic, holomorphic near `I∞`, and tends to zero
at `I∞`, then in fact it tends to zero exponentially fast. -/
theorem exp_decay_of_zero_at_inf (h_bd : is_o at_I_inf' f (1 : ℂ → ℂ) )
  (h_hol : ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ f z) :
  is_O at_I_inf' f (λ z:ℂ, real.exp (-2 * π * im z / h))  :=
begin
  have F0 := cusp_fcn_zero_of_zero_at_inf _ _ hf h_bd h_hol,
  have : f = λ z:ℂ, (cusp_fcn h f) (Q h z) := by { ext1 z, apply eq_cusp_fcn _ _ hf,},
  conv begin congr, skip, rw this, skip, funext, rw [←(abs_Q_eq h), ←norm_eq_abs], end,
  apply is_O.norm_right,
  exact (bound_holo_fcn _ (F_diff_at_zero _ _ hf h_bd.is_O h_hol) F0).comp_tendsto (Q_tendsto h),
end

end holo_at_inf_C

/-! Now we prove corresponding results about modular forms. -/

local notation `ℍ` := upper_half_plane
local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

instance : has_vadd ℝ ℍ :=
begin
  split, intros h z, refine ⟨z + h, _⟩, dsimp at *,
  suffices : 0 < complex.im (z + h), { exact this },
  rw [complex.add_im, complex.of_real_im, add_zero], exact z.2,
end

/-! Tedious checks that notions of holomorphic, bounded, etc are compatible with extension-by-0--/

section modform_equivs

variables {f : ℍ → ℂ} {k : ℤ}

lemma modform_bound_aux (C : ℝ) (g : ℂ → ℂ) (hc : 0 ≤ C)
  (h_bd : is_O_with C  upper_half_plane.at_im_infty f (λ z:ℍ, g z)) : is_O_with C at_I_inf' (extend_by_zero f) g  :=
begin

  rw is_O_with_iff at h_bd ⊢,
  apply eventually_of_mem,
  show {z : ℂ | abs(extend_by_zero f z) ≤ C * abs(g z)} ∈ at_I_inf',
  { rw at_I_inf'_mem,
    rw [upper_half_plane.at_im_infty, eventually_iff_exists_mem] at h_bd, obtain ⟨v, hv, h_bd⟩ := h_bd,
    rw [mem_comap', mem_at_top_sets] at hv, cases hv with a hv, use a,
   intros z hz, specialize hv (im z) (hz.le), dsimp at hv,
   rw extend_by_zero, dsimp, split_ifs,
   swap, { rw absolute_value.map_zero, refine mul_nonneg hc _, apply absolute_value.nonneg, },
   specialize h_bd ⟨z, h⟩,
   specialize h_bd (hv _), refl, exact h_bd },
  { dsimp, intros x hx, linarith, },
end

local notation f `∣[`:73 k:0, A `]`  :72 := slash_action.map ℂ k A f

lemma modform_bounded (k : ℤ) (f : ℍ → ℂ) (h_mod : modular_form_weight_k k ⊤ f) :
  is_O at_I_inf' (extend_by_zero f) (1 : ℂ → ℂ)  :=
begin
  have bd := h_mod.hol.bdd_at_infty,-- (1 : SL(2, ℤ)),
  have : f ∣[k, (1 : SL(2, ℤ))] = f, by {apply slash_action.one_mul},
  --rw [this, upper_half_plane.is_bounded_at_im_infty] at bd,
  obtain ⟨c, c_pos, bd⟩ := bd.exists_nonneg,
  exact (modform_bound_aux c 1 c_pos bd).is_O,
end

lemma modform_periodic (h_mod : modular_form_weight_k k ⊤ f) (z : ℂ) :
  (extend_by_zero f)(z + 1) = (extend_by_zero f)(z) :=
begin
  by_cases hz : 0 < im z,
  { rw (extend_by_zero_eq_of_mem f z hz),
    have : 0 < im (z + 1), {rw [add_im, one_im, add_zero], exact hz },
    rw (extend_by_zero_eq_of_mem f _ this),
    sorry,
  },
  {
    sorry,
  },

end

lemma modform_hol (h_mod : modular_form_weight_k k ⊤ f) (z : ℂ) (hz : 0 < im z) :
  differentiable_at ℂ (extend_by_zero f) z :=
begin

  sorry,
end

lemma modform_hol_infty (h_mod : modular_form_weight_k k ⊤ f) :
  ∀ᶠ (z : ℂ) in at_I_inf', differentiable_at ℂ (extend_by_zero f) z :=
begin
  refine eventually_of_mem (_ : upper_half_space ∈ at_I_inf') _,
  { rw at_I_inf'_mem, use 0, tauto, },
  { intros x hx, exact modform_hol h_mod x hx },
end

end modform_equivs

section modforms

def unit_disc_sset := {z : ℂ | z.abs <  1}

lemma unit_disc_is_open : is_open unit_disc_sset := is_open_Iio.preimage complex.continuous_abs

local notation `𝔻` := ( ⟨unit_disc_sset, unit_disc_is_open⟩ : topological_space.opens ℂ)

variables (f : ℍ → ℂ) (k : ℤ)

--lemma q_in_D (z : ℍ) : abs (Q 1 z) < 1 := by { convert (abs_q_lt_iff 1 0 z).mpr z.2, simp }

lemma z_in_H (q : 𝔻) (hq : (q : ℂ) ≠ 0) : 0 < im (Z 1 q) :=
begin
  rw im_Z_eq 1 q hq,
  apply mul_pos_of_neg_of_neg,
  { exact div_neg_of_neg_of_pos (neg_lt_zero.mpr zero_lt_one) real.two_pi_pos },
  rw real.log_neg_iff, exact q.2,
  apply absolute_value.pos, exact hq,
end

end modforms

