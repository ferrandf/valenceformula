/-Included in the project Formalizing Modular Forms (Ferran Delgà Fernández)
under the supervision of Marc Masdeu.-/

import algebra.module.submodule.basic
import algebra.group_power.basic
import analysis.complex.upper_half_plane.basic
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group
import algebra.direct_sum.ring
import number_theory.modular
import geometry.manifold.mfderiv
import number_theory.modular_forms.slash_actions
import number_theory.modular_forms.slash_invariant_forms
import linear_algebra.general_linear_group
import .merh

/-
# Modular forms definition:

- We define modular forms on SL₂(ℤ) and for congruence subgroups

## Main definitions:

* weakly_modular_weight_k sets the conditions for a function to be weakly modular.

* weakly_modular_submodule_weight_k is the submodule associated to the previous definition.

* class modular_form_weight_k defines modular forms.

* weakly_meromorphic_modular_weight_k defines weakly modularity for Merℍ functions. 

* Merℍwm is the subtype for meromorphic modular forms.
-/

open complex

open_locale topological_space manifold


noncomputable theory

open modular_form

open_locale upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

instance : charted_space ℂ ℂ := infer_instance

instance : charted_space ℂ ℍ' := infer_instance

local prefix `↑ₘ`:1024 := @coe _ (matrix (fin 2) (fin 2) _) _

local notation `GL(` n `, ` R `)`⁺:= matrix.GL_pos (fin n) R

local notation `SL(` n `, ` R `)`:= matrix.special_linear_group (fin n) R

variable (M : GL(2, ℝ)⁺)

open modular_form
open complex matrix matrix.special_linear_group upper_half_plane
open_locale upper_half_plane complex_conjugate

variables (Γ : subgroup SL(2,ℤ)) (C : GL(2, ℝ)⁺) (k: ℤ) (f : (ℍ → ℂ))

localized "notation  f  ` ∣[`:100 k `]`:0 γ :100 := slash k γ f" in modular_form

--Definition of modular forms:
def weakly_modular_weight_k (k : ℤ) (f : ℍ' → ℂ) :=
    ∀ (γ : SL(2,ℤ)),  (f ∣[k] (γ : GL(2, ℝ)⁺)) = f

lemma zero_weakly_modular (k : ℤ) : weakly_modular_weight_k k (0 : ℍ' → ℂ) :=
begin
intro γ,
ext1,
rw slash,
simp,
end

def one_periodicity (f : ℍ' → ℂ) := ∀ (z : ℍ'), extend_by_zero f (z + 1) = extend_by_zero f (z)

def weakly_modular_submodule_weight_k (k : ℤ) : submodule ℂ (ℍ' → ℂ) := {
  carrier := weakly_modular_weight_k k,
  zero_mem' := by {exact zero_weakly_modular k},
  add_mem' := by {
    intros f g hf hg,
    intro γ,
    have hff:= hf γ,
    have hgg:= hg γ,
    rw slash_add k γ f g,
    rw [hff, hgg],
  },
  smul_mem' := by {
    intros c f hf,
    intro γ,
    have hff:= hf γ,
    have : (c • f)  ∣[k] γ = c • (f  ∣[k] γ ),
    by {apply smul_slash},
    rw hff at this,
    apply this,
  },
}


class modular_form_weight_k (k : ℤ) (f : ℍ' → ℂ) : Prop :=
  (hol : f ∈ Holℍ)
  (weak : weakly_modular_weight_k k f)


def space_of_modular_forms_weight_k (k : ℤ) : submodule ℂ (ℍ' → ℂ) := { 
  carrier := modular_form_weight_k k,
  add_mem' := λ f g hf hg, ⟨Holℍ.add_mem' hf.hol hg.hol, (weakly_modular_submodule_weight_k k).add_mem' hf.weak hg.weak⟩,
  zero_mem' := ⟨Holℍ.zero_mem', zero_weakly_modular k⟩,
  smul_mem' := λ c f hf, ⟨⟨smul_hol _ _ hf.hol.diff, bounded_at_im_infty.smul _ hf.hol.bdd_at_infty⟩,
    (weakly_modular_submodule_weight_k k).smul_mem' c hf.weak⟩,
  }

-- Definition of modular forms for congruence subgroups:

def weakly_modular_weight_k_subgroup (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ' → ℂ) :=
  ∀ (γ : Γ),  (f ∣[k] (γ : GL(2, ℝ)⁺)) = f

lemma zero_weakly_modular_subgroup (k : ℤ) (Γ : subgroup SL(2,ℤ)) : weakly_modular_weight_k_subgroup k Γ (0 : ℍ' → ℂ) :=
begin
intro γ,
ext1,
rw slash,
simp,
end

def weakly_modular_submodule_weight_k_subgroup (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ' → ℂ) := {
  carrier := weakly_modular_weight_k_subgroup k Γ,
  zero_mem' := by {exact zero_weakly_modular_subgroup k Γ},
  add_mem' := by {
    intros f g hf hg,
    intro γ,
    have hff:= hf γ,
    have hgg:= hg γ,
    rw slash_add k γ f g,
    rw [hff, hgg],
  },
  smul_mem' := by {
    intros c f hf,
    intro γ,
    have hff:= hf γ,
    have : (c • f)  ∣[k] γ = c • (f  ∣[k] γ ),
    by {apply smul_slash},
    rw hff at this,
    apply this,
  },
}

--Space of modular forms for congruence subgroups:
class modular_form_weight_k_subgroup (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ' → ℂ) : Prop :=
  (hol : f ∈ Holℍ)
  (weak : weakly_modular_weight_k_subgroup k Γ f)

def space_of_modular_forms_weight_k_subgroup (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ' → ℂ) := { 
  carrier := modular_form_weight_k_subgroup k Γ,
  add_mem' := λ f g hf hg, ⟨Holℍ.add_mem' hf.hol hg.hol, (weakly_modular_submodule_weight_k_subgroup k Γ).add_mem' hf.weak hg.weak⟩,
  zero_mem' := ⟨Holℍ.zero_mem', zero_weakly_modular_subgroup k Γ⟩,
  smul_mem' := λ c f hf, ⟨⟨smul_hol _ _ hf.hol.diff, bounded_at_im_infty.smul _ hf.hol.bdd_at_infty⟩,
    (weakly_modular_submodule_weight_k_subgroup k Γ).smul_mem' c hf.weak⟩,
  }

-- Definition of meromorphic modular forms:
def slash_mer_left (k : ℤ) (γ : SL(2,ℤ)) (f g : ℍ → ℂ) (z : ℍ) : ℂ :=
  f(γ • z) * g(z) * (upper_half_plane.denom γ z)^(-k)

def slash_mer_right (k : ℤ) (γ : SL(2,ℤ)) (f g : ℍ → ℂ) (z : ℍ) : ℂ :=
  f(z) * g(γ • z)

def weakly_meromorphic_modular_weight_k (k : ℤ) (F : Merℍ) :=
  ∀ (γ : SL(2,ℤ)), slash_mer_left k γ F.numerator.val F.denominator.val.val = slash_mer_right k γ F.numerator.val F.denominator.val.val

instance mem_mer : has_mem Merℍ (submodule ℂ (ℍ' → ℂ)) := ⟨λ F V, F.map ∈ V⟩

--Meromorphic modular form subtype

def Merℍwm (k : ℤ) :=
{F : Merℍ // weakly_meromorphic_modular_weight_k k F}

lemma Merℍwm_def (k : ℤ) (F : Merℍwm k) : weakly_meromorphic_modular_weight_k k F.val :=
begin
exact F.prop,
end
