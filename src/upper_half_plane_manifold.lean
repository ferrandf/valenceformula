/-Included in the project Formalizing Modular Forms (Ferran Delgà Fernández)
under the supervision of Marc Masdeu.-/

import analysis.complex.upper_half_plane.topology
import geometry.manifold.mfderiv
import holomorphic_functions

local notation `ℍ`:=upper_half_plane

noncomputable theory

open_locale classical topological_space manifold
--The upper half space as a subset of `ℂ`

def upper_half_space := {z : ℂ | 0 <  z.im}

#check upper_half_space

lemma preconn_ℍ' : is_preconnected upper_half_space :=
begin
apply convex.is_preconnected,
intros z hz,
rw star_convex,
intros y hy a b ha hb hab,
rw upper_half_space,
simp,
by_cases ht : a = 0,
rw ht at hab,
simp [ht, hab], simp at hab, rw hab, simp only [one_mul], exact hy,
by_cases hr : b = 0,
rw hr at hab, 
simp [hr, hab], simp at hab, rw hab, simp only [one_mul], exact hz,
apply add_pos,
rw eq_comm at ht,
have : 0 < a,
have := ne.le_iff_lt ht,
exact this.1 ha,
exact mul_pos this hz,
rw eq_comm at hr,
have : 0 < b,
have := ne.le_iff_lt hr,
exact this.1 hb,
exact mul_pos this hy,
end

lemma hcoe : upper_half_space = coe '' (set.univ : set upper_half_plane) :=
begin
simp, refl,
end

lemma upper_half_plane_is_open: is_open upper_half_space  :=
begin
  have : upper_half_space = complex.im⁻¹' set.Ioi 0 :=
    set.ext (λ z, iff.intro (λ hz, set.mem_preimage.mp hz) $ λ hz, hz),
  exact is_open.preimage complex.continuous_im is_open_Ioi,
end

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

variable (f : ℍ' → ℂ)

instance : inhabited ℍ' :=
begin
let  x := (⟨complex.I, by {simp,} ⟩ : ℍ),
apply inhabited.mk x,
end

lemma ext_chart (z : ℍ') : (extend_by_zero f) z = (f ∘ ⇑((chart_at ℂ z).symm)) z :=
begin
simp_rw chart_at,
simp_rw extend_by_zero,
simp,
have :=  (local_homeomorph.subtype_restr_coe  (local_homeomorph.refl ℂ) ℍ').symm,
congr,
simp_rw local_homeomorph.subtype_restr,
simp,
have hf:= topological_space.opens.local_homeomorph_subtype_coe_coe ℍ',
simp_rw ← hf,
apply symm,
apply local_homeomorph.left_inv,
simp only [topological_space.opens.local_homeomorph_subtype_coe_source],
end
