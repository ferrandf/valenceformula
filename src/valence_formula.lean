import .mod_f
import .hol_bdd
import number_theory.modular
import algebra.big_operators.basic
import .q_expansion
import analysis.complex.unit_disc.basic
import number_theory.modular
--import data.nat.lattice


open complex

open_locale big_operators classical


noncomputable theory

open modular_form modular_group complex filter asymptotics

open_locale upper_half_plane real topological_space manifold filter

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

--instance : charted_space ℂ ℂ := infer_instance

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

instance : has_coe 𝒟ᵒ 𝒟 := 
begin
sorry,
end

instance coe_fdo : has_coe (set 𝒟ᵒ) (set 𝒟) := ⟨λ U, has_coe.coe '' U⟩


def S₁' (F: Merℍ) : set (frontier 𝒟) := {z | F.order ≠ 0} 
lemma S₁'_finite (F : Merℍ) : (S₁' F).finite := by sorry
def S₁ (F : Merℍ) := set.finite.to_finset (S₁'_finite F)


def S_set (F : Merℍ) : set 𝒟 := {z | F.order ≠ 0}

instance coe_fd_ℍ : has_coe 𝒟 ℍ := 
begin
sorry,
end

instance coe_fd_ℍ_set : has_coe (set 𝒟) (set ℍ') := ⟨λ U, subtype.val '' U⟩

--Valuation at infty

--Valuation at ∞ of a Holℍ function:

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

def q_expansion_an (n : ℕ) (y : ℝ) (hy : y>0) (f : Holℍ) (hf : one_periodicity f)
: ℂ := exp(2 * π * n * y) * ∫ (x : ℝ) in 0..1, ( exp (-2 * π * I * n *(map_to_upper x y hy))) * f.val (map_to_upper x y hy)

variables {s : set ℕ}
def vtst (hs : s.nonempty) : ℕ := Inf s
example (hs : s.nonempty) : vtst hs ∈ s:=
begin
exact Inf_mem hs,
end



def val_infty_Holℍ (f : Holℍ) (hf : one_periodicity f) (y0 : ℝ) (hy0 : y0 > 0) : ℕ := 
Inf {n | (q_expansion_an n y0 hy0 f hf) ≠ 0}
--aquí hauria de ser min dels n ∈ ℕ tal que modular_form_an ≠ 0

example  (f : Holℍ) (k : ℤ) (hf : one_periodicity f)
: q_expansion_an (val_infty_Holℍ f hf) 1 k f.val hf ≠ 0 :=
begin
  change val_infty_Holℍ f k hf ∈ {n | modular_form_an n f.val hf ≠ 0},
  apply nat.Inf_mem _,
  sorry
end


def val_infty (k : ℤ) (F : Merℍwm k) : ℤ := sorry /-(k1 k2 : ℤ) (k : ℤ) (Γ : subgroup SL(2,ℤ)) (F : Merℍwm k Γ) : ℤ := -/


theorem valence_formula (k : ℤ) (F : Merℍwm k) :
  6 * val_infty k F.val + 3 * val_i F.val + 2 * val_rho F.val + 6 * ∑ τ in (S₀ F.val), (F.val.order τ) + 12 * ∑ τ in (S₁ F.val), (F.val.order τ) = k/2 :=
begin

sorry,
end
