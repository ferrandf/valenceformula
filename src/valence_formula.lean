import number_theory.modular
import algebra.big_operators.basic
import analysis.complex.unit_disc.basic
--import .q_expansion
import .mod_f

/-
# Valence formula statement:

- We add a the bounded at im_infty property to our previously defined 
  is_holomorphic_on functions using results in 
  analysis.complex.upper_half_plane.functions_bounded_at_infty.

## Main definitions:

* class is_holomoprhic_bdd: sets the conditions any f : ℍ' → ℂ has to satisfy; 

* pseries_of_holomorphic: is the power series of a given is_holomorphic_bdd function;

* We define the order of a is_holomoprhic_bdd function at a given point.

## Main results:

* Any function thas satisfies is_holomorphic_bdd is also analytic using 
  its extension by zero (from file: holomorphic_functions.lean).

* The pseries_of_holomorphic is the formal_multilinear_series of the function.

* The order is well defined.

-/

open complex
open_locale big_operators classical
noncomputable theory

open modular_form modular_group complex filter asymptotics

open_locale upper_half_plane real topological_space manifold filter

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

instance : charted_space ℂ ℍ' := infer_instance

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _
local notation `GL(` n `, ` R `)`⁺:= matrix.GL_pos (fin n) R
local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

localized "notation (name := modular_group.fd) `𝒟` := modular_group.fd" in modular

localized "notation (name := modular_group.fdo) `𝒟ᵒ` := modular_group.fdo" in modular

--Definitions of orders/valuations

def val_i (F : Merℍ) := F.order (⟨(⟨0, 1⟩ : ℂ), by {simp only [zero_lt_one],} ⟩ : ℍ)

def val_rho (F : Merℍ) := F.order (⟨(⟨-0.5, (real.sqrt (3 : ℝ))*0.5⟩ : ℂ), by {simp,} ⟩ : ℍ)

def S₀' (F : Merℍ) : set 𝒟ᵒ := {z | F.order z ≠ 0}
lemma S₀'_finite (F : Merℍ) : (S₀' F).finite := by sorry
def S₀ (F : Merℍ) := set.finite.to_finset (S₀'_finite F)


def S₁' (F: Merℍ) : set (frontier 𝒟) := {z | F.order ≠ 0} 
lemma S₁'_finite (F : Merℍ) : (S₁' F).finite := by sorry
def S₁ (F : Merℍ) := set.finite.to_finset (S₁'_finite F)


localized "notation `𝔻` := complex.unit_disc" in unit_disc

local notation `𝔻'` := ( ⟨unit_disc_sset, unit_disc_is_open⟩ : topological_space.opens ℂ)
instance : has_zero 𝔻' := 
begin
  simp only [coe_sort_coe_base, subtype.coe_mk],
  have : (0 : ℂ).abs < 1,
  {
    simp only [absolute_value.map_zero, zero_lt_one],
  },
  rw unit_disc_sset,
  use 0,
  exact this,
end

def map_to_upper (x : ℝ) (y : ℝ) (hy : y>0) : ℍ := ⟨(x + y*I),
  by {
    simp only [complex.add_im, complex.of_real_im, zero_add, complex.of_real_mul_im,complex.I_im, mul_one],
    exact hy,
    } ⟩

def q_expansion_an (n : ℤ) (y : ℝ) (hy : y>0) (f : Merℍ) (hf : one_periodicity f.map)
: ℂ := exp(2 * π * n * y) * ∫ (x : ℝ) in 0..1, ( exp (-2 * π * I * n *(map_to_upper x y hy))) * f.map (map_to_upper x y hy)

variables {s : set ℕ}
def vtst (hs : s.nonempty) : ℕ := Inf s
example (hs : s.nonempty) : vtst hs ∈ s:=
begin
exact Inf_mem hs,
end


def val_infty_Merℍ (f : Merℍ) (hf : one_periodicity f.map) (y0 : ℝ) (hy0 : y0 > 0) : ℤ := sorry
--Inf {n : ℤ | (q_expansion_an n y0 hy0 f hf) ≠ 0}

lemma Merℍ.is_oneperiodic (k : ℤ) (F : Merℍwm k) : one_periodicity F.val.map :=
begin
sorry,
end

theorem valence_formula (k : ℤ) (F : Merℍwm k) :
  6 * (val_infty_Merℍ F.val (Merℍ.is_oneperiodic k F) 1 one_pos) + 3 * (val_i F.val) + 2 * (val_rho F.val)
  + 6 * ∑ τ in (S₀ F.val), (F.val.order τ) + 12 * ∑ τ in (S₁ F.val), (F.val.order τ) = k/2 := by sorry
