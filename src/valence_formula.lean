/-Included in the project Formalizing Modular Forms (Ferran Delgà Fernández)
under the supervision of Marc Masdeu.-/

import number_theory.modular
import algebra.big_operators.basic
import analysis.complex.unit_disc.basic
import analysis.complex.removable_singularity
import analysis.complex.upper_half_plane.basic
import analysis.complex.upper_half_plane.topology
import number_theory.modular
import group_theory.index
import order.upper_lower
import mod_f

/-
# Valence formula statement:

- We define the last definitions and lemmas needed for the statement of the valence formula.

## Main definitions:

* Valuations of i and ρ.

* Sets containing the zeros and poles of a given Merℍ function F that are inside 
  the fundamental domain or its boundary. 

* The a_n coefficients of the q-expansion of F.

* The valuation at ∞ of a given Merℍ. 
-/

open modular_form complex filter asymptotics
open_locale big_operators classical real topological_space manifold filter
noncomputable theory

open modular_form modular_group complex filter asymptotics

open_locale upper_half_plane real topological_space manifold filter

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _
local notation `GL(` n `, ` R `)`⁺:= matrix.GL_pos (fin n) R
local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

localized "notation (name := modular_group.fd) `𝒟` := modular_group.fd" in modular

localized "notation (name := modular_group.fdo) `𝒟ᵒ` := modular_group.fdo" in modular


--Definitions of orders/valuations:

def val_i (F : Merℍ) := F.order (⟨(⟨0, 1⟩ : ℂ), by {simp only [zero_lt_one],} ⟩ : ℍ)

def val_rho (F : Merℍ) := F.order (⟨(⟨-0.5, (real.sqrt (3 : ℝ))*0.5⟩ : ℂ), by {simp,} ⟩ : ℍ)

-- Definitions of S₀ and S₁ sets:

def S₀' (F : Merℍ) : set 𝒟ᵒ := {z | F.order z ≠ 0}
lemma S₀'_finite (F : Merℍ) : (S₀' F).finite := by sorry
def S₀ (F : Merℍ) := set.finite.to_finset (S₀'_finite F)


def S₁' (F: Merℍ) : set (frontier 𝒟) := {z | F.order ≠ 0} 
lemma S₁'_finite (F : Merℍ) : (S₁' F).finite := by sorry
def S₁ (F : Merℍ) := set.finite.to_finset (S₁'_finite F)


def map_to_upper (x : ℝ) (y : ℝ) (hy : y>0) : ℍ := ⟨(x + y*I),
  by {
    simp only [complex.add_im, complex.of_real_im, zero_add, complex.of_real_mul_im,complex.I_im, mul_one],
    exact hy,
    } ⟩

def q_expansion_an (n : ℤ) (y : ℝ) (hy : y>0) (f : Merℍ) (hf : one_periodicity f.map)
: ℂ := exp(2 * π * n * y) * ∫ (x : ℝ) in 0..1, ( exp (-2 * π * I * n *(map_to_upper x y hy))) * f.map (map_to_upper x y hy)


def set_coeffs (y : ℝ) (hy : y>0) (f : Merℍ) (hf : one_periodicity f.map) :  set ℤ :=
{n : ℤ | (q_expansion_an n y hy f hf) ≠ 0}


lemma set_coeffs_is_bdd_below (y : ℝ) (hy : y>0) (f : Merℍ) (hf : one_periodicity f.map) :
bdd_below (set_coeffs (y : ℝ) (hy : y>0) (f : Merℍ) (hf : one_periodicity f.map)) := sorry

lemma set_coeffs_nonempty (y : ℝ) (hy : y>0) (f : Merℍ) (hf : one_periodicity f.map) :
∃ n : ℤ, n ∈ (set_coeffs (y : ℝ) (hy : y>0) (f : Merℍ) (hf : one_periodicity f.map)) := sorry

def val_infty_Merℍ (f : Merℍ) (hf : one_periodicity f.map) (y : ℝ) (hy: y > 0) : ℤ :=
classical.some (int.exists_least_of_bdd (set_coeffs_is_bdd_below y hy f hf)
(set_coeffs_nonempty y hy f hf))

lemma Merℍ.is_oneperiodic (k : ℤ) (F : Merℍwm k) : one_periodicity F.val.map :=
begin
unfold one_periodicity,
intro z,
have h := F.prop T,
/-have hw : slash_mer_left k T F.val.numerator.val F.val.denominator.val.val z = slash_mer_right k T F.val.numerator.val F.val.denominator.val.val z,
sorry,
rw slash_mer_left_def k T F.val.numerator.val F.val.denominator.val.val z at hw,
rw slash_mer_right_def k T F.val.numerator.val F.val.denominator.val.val z at hw,
have : (F.val.numerator.val (↑T • z) / F.val.denominator.val.val (↑T • z)) * upper_half_plane.denom ↑T z ^ -k = F.val.numerator.val z / F.val.denominator.val.val z,
{
  sorry,
},
rw Merℍ.map,-/
sorry,
end

theorem valence_formula (k : ℤ) (F : Merℍwm k) :
  6 * (val_infty_Merℍ F.val (Merℍ.is_oneperiodic k F) 1 one_pos) + 3 * (val_i F.val) + 2 * (val_rho F.val)
  + 6 * ∑ τ in (S₀ F.val), (F.val.order τ) + 3 * ∑ τ in (S₁ F.val), (F.val.order τ) = k/2 := by sorry

/- Definition of q(z), z(q)...-/

def Q (z : ℂ) : ℂ := exp ( 2 * π * I * z )

def Z (q : ℂ) : ℂ := 1 / (2 * π * I) * log q

lemma log_exp' (z : ℂ) : ∃ (n : ℤ), log (exp z) = z + n * (2 * π * I) :=
begin
  rw [←exp_eq_exp_iff_exists_int, exp_log], exact exp_ne_zero z,
end

lemma QZ_eq_id (q : ℂ) (hq : q ≠ 0) : Q (Z q) = q :=
begin
  dsimp only [Q, Z],
  suffices : 2 * ↑π * I * (1 / (2 * ↑π * I) * log q) = log q,
  {
    rw this,
    exact exp_log hq,
  },
  simp only [one_div],
  field_simp [two_pi_I_ne_zero],
  ring,
end

lemma abs_Q_eq (z : ℂ) : abs (Q z) = real.exp(-2 * π * im z ) :=
begin
  dsimp only [Q], rw abs_exp, congr,
  --rw mul_assoc,
  have : 2 * ↑π * I * z = (↑(2 * π) * z) * I := by { simp, ring, },
  simp [this, mul_I_re, of_real_mul_im],
end

lemma im_Z_eq (q : ℂ) (hq : q ≠ 0) : im (Z q) = -1 / (2 * π) * real.log (abs q) :=
begin
  dsimp only [Z],
  have : 1 / (2 * ↑π * I) * log q = - 1 / (2 * ↑π) * log q * I,
  { 
    field_simp [of_real_ne_zero.mpr real.pi_pos.ne', two_pi_I_ne_zero],
    ring_nf,
    simp,
  },
  rw [this, mul_I_im],
  have : -1 / (2 * ↑π) * log q = ↑(-1 / (2 * π)) * log q := by simp,
  rw [this, of_real_mul_re, log_re],
end

lemma ZQ_eq_mod_period (z : ℂ) : ∃ (m : ℤ), Z (Q z) = z + m :=
begin
  dsimp only [Q, Z],
  have t := log_exp' ( 2 * ↑π * I * z ),
  cases t with m t, use m, rw t,
  field_simp [two_pi_I_ne_zero], ring,
end

lemma abs_q_lt_iff (A : ℝ) (z : ℂ) : abs (Q z) < real.exp(-2 * π * A ) ↔ A < im z :=
begin
  rw [abs_Q_eq, real.exp_lt_exp],
  split,
  { 
    intro hz,
    have : (-2) * π < 0 := by simpa using real.pi_pos,
    rwa mul_lt_mul_left_of_neg this at hz,
  },
  { 
    intro hz,
    have : (-2) * π < 0 := by simpa using real.pi_pos,
    rwa mul_lt_mul_left_of_neg this,
  },
end

-- Use filters

def at_I_infi : filter ℂ := at_top.comap im

lemma at_I_infi_mem (S : set ℂ) : S ∈ at_I_infi ↔ (∃ A : ℝ, ∀ z : ℂ, A < im z → z ∈ S) :=
begin
  rw [at_I_infi, mem_comap', mem_at_top_sets],
  simp, split,
  { 
    intro h,
    cases h with a h, use a,
    intros z hz,
    specialize h (im z) hz.le, apply h, refl 
  },
  { 
    intro h,
    cases h with A h, use A + 1,
    intros b hb x hx,
    apply (h x), rw hx, linarith,
  }
end

lemma Z_tendsto : tendsto (Z) (𝓝[{0}ᶜ] 0) at_I_infi :=
begin
  rw [tendsto, map_le_iff_le_comap, comap],
  intros S h, simp_rw at_I_infi_mem at h, obtain ⟨T, ⟨A, hA⟩, hT⟩ := h,
  simp_rw [metric.mem_nhds_within_iff, metric.ball, dist_eq, sub_zero],
  use real.exp(-2 * π * A ), split, apply real.exp_pos,
  intro q, dsimp, rintro ⟨u1, u2⟩,
  rw [←(QZ_eq_id _ u2), abs_q_lt_iff] at u1, specialize hA (Z q) u1,
  apply hT, exact hA,
end

lemma Q_tendsto : tendsto (Q) at_I_infi (𝓝 0) :=
begin
  rw [tendsto_zero_iff_norm_tendsto_zero],
  simp_rw [norm_eq_abs,abs_Q_eq],
  have : set.range im ∈ at_top,
  { suffices : set.range im = ⊤, { rw this, apply univ_mem, },
    ext1, simp only [set.mem_range, set.top_eq_univ, set.mem_univ, iff_true],
    use I * x, simp, },
  have := (@tendsto_comap'_iff ℝ ℝ ℂ (λ y, real.exp ((-2) * π * y)) at_top (𝓝 0) im this).mpr,
  apply this, refine real.tendsto_exp_at_bot.comp _,
  apply tendsto.neg_const_mul_at_top, { simpa using real.pi_pos }, exact tendsto_id,
end

section G_dfn

variables (f : ℂ → ℂ) (hf : ∀ (z : ℂ), f(z + 1) = f(z))

def G_0 : ℂ → ℂ := λ q, f (Z q)

def G : ℂ → ℂ := function.update (G_0 f) 0 (lim (𝓝[≠] (0 : ℂ)) (G_0 f))

lemma G_eq_of_nonzero (q : ℂ) (hq : q ≠ 0) :
  (G f) q = (G_0 f) q :=
begin
  rw [G, function.update],
  split_ifs,
  { 
    exfalso,
    exact hq h,
  },
  refl,
end

lemma is_periodic_aux (z : ℂ) (n : ℕ) (hf : ∀ (z : ℂ), f(z + 1) = f(z)) : f (z + n) = f z :=
begin
  induction n with n hn generalizing z, simp,
  rw [nat.succ_eq_add_one, nat.cast_add, nat.cast_one, ←add_assoc],
  rw hf (z + n),
  exact hn z,
end

lemma is_periodic (z : ℂ) (n : ℤ) (hf : ∀ (z : ℂ), f(z + 1) = f(z)): f (z + n) = f z :=
begin
  cases n,
  exact is_periodic_aux f z n hf,
  simp only [neg_add_rev, int.cast_neg_succ_of_nat],
  convert (is_periodic_aux f (z-(n+1)) (n+1) hf).symm,
  simp, ring,
  simp only [nat.cast_add, algebra_map.coe_one, sub_add_cancel],
end

lemma eq_G (z : ℂ) (hf : ∀ (z : ℂ), f(z + 1) = f(z)) : f z = (G f) (Q z) :=
begin
  have : (G f) (Q z) = (G_0 f) (Q z),
  { 
    rw G, rw function.update, split_ifs,
    { 
      exfalso,
      have : Q z ≠ 0 := by apply exp_ne_zero,
      exact this h,
    },
    refl,
  },
  rw this,
  dsimp only [G_0],
  obtain ⟨n, hn⟩ := ZQ_eq_mod_period z,
  rw hn,
  exact (is_periodic f z n hf ).symm,
end

end G_dfn