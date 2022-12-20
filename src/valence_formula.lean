import .mod_f
import .hol_bdd
import number_theory.modular
import algebra.big_operators.basic

open complex

open_locale topological_space manifold 


noncomputable theory

open modular_form modular_group

open_locale upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

instance : charted_space ℂ ℂ := infer_instance

instance : charted_space ℂ ℍ' := infer_instance

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺:= matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

localized "notation (name := modular_group.fd) `𝒟` := modular_group.fd" in modular

localized "notation (name := modular_group.fdo) `𝒟ᵒ` := modular_group.fdo" in modular


-- Valuation of ∞:


--Definitions of valuations

def val_i (F : Merℍ) := F.order (⟨(⟨0, 1⟩ : ℂ), by {simp only [zero_lt_one],} ⟩ : ℍ)

def val_rho (F : Merℍ) := F.order (⟨(⟨-0.5, (real.sqrt (3 : ℝ))*0.5⟩ : ℂ), by {simp,} ⟩ : ℍ)

def S₀ (F : Merℍ) : set 𝒟ᵒ := {z | F.order z ≠ 0}

instance : has_coe 𝒟ᵒ 𝒟 := 
begin
sorry,
end

instance coe_fdo : has_coe (set 𝒟ᵒ) (set 𝒟) := ⟨λ U, has_coe.coe '' U⟩


def S₁ (F: Merℍ) : set (frontier 𝒟) := {z | F.order ≠ 0} 

lemma S₀_is_discrete (F : Merℍ) : discrete_topology (S₀ F) :=
begin

sorry,
end

lemma S₁_is_discrete (F : Merℍ) : discrete_topology (S₁ F) :=
begin

sorry,
end

def S_set (F : Merℍ) : set 𝒟 := {z | F.order ≠ 0}

instance coe_fd_ℍ : has_coe 𝒟 ℍ := 
begin
sorry,
end

instance coe_fd_ℍ_set : has_coe (set 𝒟) (set ℍ') := ⟨λ U, subtype.val '' U⟩

/-lemma S_as_intersec (F : Merℍ) : (S_set F : set ℍ') = 𝒟 ∩ F.zeros :=
begin
sorry,
end-/

theorem valence_formula (k : ℤ) (Γ : subgroup SL(2,ℤ)) (F : space_of_meromorphic_modular_forms_weight_k k Γ) :
  1/2 * val_i F + 1/3 * val_rho F + ∑ τ in (S₀ F), (F.order τ) + ∑ τ in (S₁ F), (2*(F.order τ)) = k/12 :=
begin
sorry,
end