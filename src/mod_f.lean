import algebra.module.submodule.basic
import algebra.group_power.basic
import .holomorphic_functions
import analysis.complex.upper_half_plane.basic
import linear_algebra.general_linear_group
import linear_algebra.special_linear_group
import algebra.direct_sum.ring
import number_theory.modular
import geometry.manifold.mfderiv
import .upper_half_plane_manifold
import .hol_bdd
import number_theory.modular_forms.slash_actions
import number_theory.modular_forms.slash_invariant_forms

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

lemma auxmf2 (a b c : ℂ) : b⁻¹*c⁻¹*a=(b*c)⁻¹*a:=
begin
field_simp,
end

lemma aux1 (a b c d e: ℂ) (k : ℤ) : (e^k)⁻¹*a^(k-1) * (b^k)⁻¹ * c^(k -1) * d =
( (b * e)^ k)⁻¹ * (c * a)^(k-1) * d:=
begin
have : (b^k)⁻¹ * ((e)^ k)⁻¹ * (c)^(k-1) * (a)^(k-1) * d = ( (b * e)^ k)⁻¹ * (c * a)^(k-1) * d ,
 by  {ring_exp, rw ← mul_assoc,
 have:  (b * e)^ k = b^k * e^k, by {exact mul_zpow b e k,},
 simp_rw [mul_zpow],
 simp_rw [mul_inv],ring,},
rw ←this,
ring,
end

open modular_form

variables (Γ : subgroup SL(2,ℤ)) (C : GL(2, ℝ)⁺) (k: ℤ) (f : (ℍ → ℂ))

localized "notation  f  ` ∣[`:100 k `]`:0 γ :100 := slash k γ f" in modular_form

def weakly_modular_weight_k (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ' → ℂ) :=
  ∀ (γ : Γ),  (f ∣[k] (γ : SL(2, ℝ))) = f

lemma zero_weakly_modular (k : ℤ) (Γ : subgroup SL(2,ℤ)) : weakly_modular_weight_k k Γ (0 : ℍ' → ℂ) :=
begin
intro γ,

sorry,
end

def weakly_modular_submodule_weight_k (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ' → ℂ) := {
  carrier := weakly_modular_weight_k k Γ,
  zero_mem' := by {
    dsimp,
  },
  add_mem' := _,
  smul_mem' := _,
}

class modular_form_weight_k (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ' → ℂ) : Prop :=
  (hol : f ∈ Holℍ)
  (weak : weakly_modular_weight_k k Γ f)

instance : has_mem Merℍ (submodule ℂ (ℍ' → ℂ)) := ⟨λ f V, (λ z, (f.numerator.val z / f.denominator.val.val z)) ∈ V⟩

class meromorphic_modular_form_weight_k (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : Merℍ) : Prop :=
  (weak : f ∈ weakly_modular_submodule_weight_k k Γ)

def space_of_modular_forms_weight_k (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ' → ℂ) := { 
  carrier := modular_form_weight_k k Γ,
  add_mem' := _,
  zero_mem' := _,
  smul_mem' := _,
  }


def space_of_mer_modular_forms_weight_k (k : ℤ) (Γ : subgroup SL(2,ℤ)) : submodule ℂ (ℍ' → ℂ) := {
  carrier := {f : Merℍ | weakly_modular_weight_k k Γ f.val},
  add_mem' := _,
  zero_mem' := _,
  smul_mem' := _,
}



def weakly_modular_submodule (k : ℤ)  (Γ : subgroup SL(2,ℤ)): submodule ℂ (ℍ  → ℂ) := {
  carrier := {f : (ℍ → ℂ) | ∀ (γ : Γ),  (f ∣[k] (γ : GL(2, ℝ)⁺)) = f },
  zero_mem' := by {simp only [set.mem_set_of_eq, coe_coe],
  simp_rw slash,
  simp only [forall_const, zero_mul, pi.zero_apply],
  refl, },
  add_mem' := by {intros f g hf hg,
  simp only [set.mem_set_of_eq, coe_coe] at *,
  intro γ,
  have hff:= hf γ,
  have hgg:= hg γ,
  rw [←coe_coe, ←coe_coe] at *,
  rw slash_add k γ f g,
  rw [hff, hgg], },
  smul_mem' := by {intros c f hf,
  simp only [set.mem_set_of_eq, coe_coe] at *,
  intro γ,
  have hff:= hf γ,
  have : (c • f)  ∣[k] γ = c • (f  ∣[k] γ ),
  by {apply smul_slash},
  rw ←  coe_coe at *,
  rw ←  coe_coe at *,
  rw hff at this,
  apply this,}}

lemma wmodular_mem (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔  ∀ (γ : Γ), (f ∣[k] (γ : GL(2, ℝ)⁺)) = f := iff.rfl

/--A function `f:ℍ → ℂ` is modular, of level `Γ` and weight `k ∈ ℤ`, if for every matrix in
 `γ ∈  Γ` we have `f(γ  • z)= (c*z+d)^k f(z)` where `γ= ![![a, b], ![c, d]]`,
 and it acts on `ℍ` via Moebius trainsformations. -/
@[simp] lemma wmodular_mem' (k : ℤ) (Γ : subgroup SL(2,ℤ)) (f : ℍ → ℂ) :
  f ∈ (weakly_modular_submodule k Γ) ↔  ∀ γ : Γ, ∀ z : ℍ,
  f ((γ : matrix.GL_pos (fin 2) ℝ) • z) = ((↑ₘγ 1 0 : ℝ) * z +(↑ₘγ 1 1 : ℝ))^k * f z :=
begin
  simp only [wmodular_mem],
  split,
  intros h1 γ z,
  have h2:= h1 γ,
  have h3: (f ∣[k] γ) z = f z , by {simp_rw h2},
  rw ← h3,
  simp_rw slash,
  rw mul_comm,
  have h5:= upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z,
  simp only [coe_fn_coe_base, ne.def, matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at h5,
  have pown := zpow_ne_zero k h5,
  have h55:= inv_mul_cancel pown,
  simp_rw upper_half_plane.denom at *,
  simp only [coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
  matrix.special_linear_group.coe_matrix_coe, int.coe_cast_ring_hom,
  matrix.map_apply, of_real_int_cast],
  simp [matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix] at h55,
  rw mul_assoc,
  simp_rw [h55],
  simp,
  simp_rw [←int.coe_cast_ring_hom],
  simp_rw ←matrix.special_linear_group.coe_matrix_coe,
  have := matrix.special_linear_group.det_coe ((γ : SL(2, ℤ) ) : SL(2, ℝ)),
  rw this,
  simp,
  sorry,
  intros hf γ,
  simp_rw slash,
  ext1,
  have hff:= hf γ x,
  rw hff,
  rw mul_comm,
  have h5:= upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) x,
  simp only [coe_fn_coe_base, ne.def, matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at h5,
  have pown := zpow_ne_zero k h5,
  have h55:= inv_mul_cancel pown,
  simp_rw upper_half_plane.denom at *,
  simp [matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix] at h55,
  simp only [coe_coe, matrix.special_linear_group.coe_GL_pos_coe_GL_coe_matrix,
  matrix.map_apply, of_real_int_cast],
  have := matrix.special_linear_group.det_coe ((γ : SL(2, ℤ) ) : SL(2, ℝ)),
  rw this,
  simp,
  rw ← mul_assoc,
  simp_rw h55,
  simp,
end

lemma mul_modular  (k_1 k_2 : ℤ) (Γ : subgroup SL(2,ℤ)) (f g : ℍ → ℂ)
  (hf : f ∈  weakly_modular_submodule k_1 Γ)  (hg : g ∈ weakly_modular_submodule k_2 Γ) :
  f * g  ∈  weakly_modular_submodule (k_1+k_2) Γ :=
begin
  simp only [wmodular_mem', pi.mul_apply, coe_coe] at *,
  intros γ z,
  have hff:= hf γ z,
  have hgg:= hg γ z,
  rw [hff,hgg],
  have h5:= upper_half_plane.denom_ne_zero (γ : GL(2, ℝ)⁺) z,
  simp_rw upper_half_plane.denom at h5,
  simp only [coe_fn_coe_base, ne.def, matrix.general_linear_group.coe_fn_eq_coe, coe_coe] at h5,
  have pown := zpow_add₀ h5 k_1 k_2,
  rw pown,
  ring,
end

/--The extension of a function from `ℍ` to `ℍ'`-/
def hol_extn (f : ℍ → ℂ) : ℍ' → ℂ := λ (z : ℍ'), (f (z : ℍ) )



