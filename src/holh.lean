/-Included in the project Formalizing Modular Forms (Ferran Delgà Fernández)
under the supervision of Marc Masdeu.-/

import hol_bdd

/-
# Holomorphic and bounded at im_infty functions subring definition (Holℍ):

- We need our previous functions (is_holomorphic_bdd) to form a subring in order to
  complete our definition of the meromorphic functions.

## Main definitions:

* Holℍ is the subring of ℍ' → ℂ functions such that satisfy is_holomoprhic_bdd; 

* We define the order of a given Holℍ function;

## Main results:

* Holℍ is an integral domain (is_domain Holℍ).

* Holℍ is an algebra (algebra ℂ Holℍ). 

-/

open_locale classical
noncomputable theory

open_locale topological_space upper_half_plane
open complex set upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

variables (f : ℍ' → ℂ) [is_holomorphic_bdd f] (z : ℍ')

lemma const_is_bounded (c : ℂ) : is_bounded_at_im_infty (λ z : ℍ', c) :=
begin
simp only [bounded_mem],
use c.abs, use 0,
intros z hz,
linarith,
end

lemma smul_bounded {f : ℍ' → ℂ} (c : ℂ) (hf : is_bounded_at_im_infty f) : is_bounded_at_im_infty (c • f) :=
begin
apply is_bounded_at_im_infty.mul (const_is_bounded c) hf,
end

noncomputable def Holℍ : subring (ℍ' → ℂ) := {
  carrier := is_holomorphic_bdd,
  mul_mem' := λ f g hf hg, ⟨mul_hol f g hf.diff hg.diff, 
  is_bounded_at_im_infty.mul hf.bdd_at_infty hg.bdd_at_infty⟩,
  one_mem' := ⟨one_hol ℍ', const_is_bounded 1⟩,
  add_mem' := λ f g hf hg, ⟨add_hol f g hf.diff hg.diff,
  hf.bdd_at_infty.add hg.bdd_at_infty⟩,
  zero_mem' := ⟨zero_hol ℍ', zero_form_is_bounded_at_im_infty⟩,
  neg_mem' := λ f hf, ⟨neg_hol f hf.diff,hf.bdd_at_infty.neg_left⟩
}

instance is_holomorphic_on' (f : Holℍ) : is_holomorphic_bdd f := 
subring.mem_carrier.mpr f.property

def Holℍ.order (f : Holℍ) (z : ℍ) : ℤ := @hol_order f.val f.property z

lemma pseries_neq_zero_function_neq_zero (z : ℍ') (f : Holℍ)  
(hp : (pseries_of_holomorphic f z) ≠ 0): 
f.val ≠ (0 : ℍ' → ℂ) :=
begin
  intro h,
  have hc : (pseries_of_holomorphic f z) = 0,
  {
    have j : extend_by_zero f.val = 0,
    {
      rw h,
      exact extend_by_zero_zero',
    },
    have p : has_fpower_series_at (extend_by_zero f.val) (pseries_of_holomorphic f z) z,
    {
      apply pseries_of_holomorphic_def,
    },
    rw j at p,
    rw has_fpower_series_at.eq_zero p,
  },
  exact hp hc,
end

lemma hol_bdd.eventually_eq_zero_everywhere (f : Holℍ) 
  (x : ℍ') (hF : ∀ᶠ z in 𝓝 x, (extend_by_zero f.val) z = 0):
  (extend_by_zero f.val) = (0 : ℂ → ℂ) :=
begin
have hf := analytic_on_of_holomorphic f,
have tf := analytic_on.eq_on_zero_of_preconnected_of_eventually_eq_zero hf preconn_ℍ' x.prop hF,
simp at tf ⊢,
rw extend_by_zero,
apply funext, intros y,
by_cases hy : y ∈ upper_half_space,
{
  simp [hy],
  intro h,
  specialize tf hy,
  rw extend_by_zero_eq_of_mem _ _ h at tf,
  exact tf,
},
{
  simp [hy],
  intro h,
  contradiction,
}
end


lemma function_neq_zero_forall_z_pseries_neq_zero (f : Holℍ)
(hf : f ≠ 0) : ∀ z : ℍ', (pseries_of_holomorphic f z) ≠ 0 :=
begin
intro z,
have it : f.val ≠ (0 : ℍ' → ℂ),
{
  simp only [subtype.val_eq_coe, ne.def, subring.coe_eq_zero_iff],
  exact hf,
},
intro h,
apply it,
apply extend_by_zero_f_eq_zero,
set F := pseries_of_holomorphic f z with hF,
have G : has_fpower_series_at (extend_by_zero f.val) F z := by {apply pseries_of_holomorphic_def},
rw h at G,
have l := has_fpower_series_at.eventually_eq_zero G,
exact hol_bdd.eventually_eq_zero_everywhere f z l,
end

example (z : ℂ) (U : set ℂ) (hU : is_open U) (hz : z ∈ U): (U ∩ {z}ᶜ).nonempty :=
begin
rw metric.is_open_iff at hU,
specialize hU z hz,
rcases hU with ⟨ε, ⟨hε1, hε2⟩⟩,
use z + ε/2,
apply mem_inter,
{
  apply hε2,
  simp,
  rw abs_of_pos hε1,
  linarith,
},
{
  simp,
  exact ne_of_gt hε1,
}
end


lemma hkey (z : ℂ) (U V V': set ℂ) (hU : U ∈ 𝓝 z) 
(hV : {z}ᶜ ⊆ V) (hV' : {z}ᶜ ⊆ V') : 
∃ (w : ℂ), w ∈ U ∩ (V ∩ V') ∧ w ≠ z :=
begin
rw mem_nhds_iff at hU,
rcases hU with ⟨U',⟨hU'U,is_open_U', hzU'⟩⟩,
rw metric.is_open_iff at is_open_U',
specialize is_open_U' z hzU',
rcases is_open_U' with ⟨ε, ⟨hε1, hε2⟩⟩,
use z + ε/2,
split,
{
  apply mem_inter,
  {
    apply hU'U,
    apply hε2,
    simp only [metric.mem_ball, dist_self_add_left, norm_eq_abs, map_div₀, abs_of_real, complex.abs_two],
    rw abs_of_pos hε1,
    linarith,
  },
  {
    apply (subset_inter hV hV'),
    simp only [mem_compl_iff, mem_singleton_iff, add_right_eq_self, div_eq_zero_iff, of_real_eq_zero, bit0_eq_zero, one_ne_zero,
    or_false],
    exact ne_of_gt hε1,
  }
},
{
  simp only [ne.def, add_right_eq_self, div_eq_zero_iff, of_real_eq_zero, bit0_eq_zero, one_ne_zero, or_false],
  exact ne_of_gt hε1,
}
end

lemma Holℍ_eq_zero_or_eq_zero_of_mul_eq_zero (f g : Holℍ) : f * g = 0 →  f = 0 ∨ g = 0 :=
begin
  contrapose,
  intro h,
  push_neg at h,
  cases h with hf_ne_zero hg_ne_zero,
    let i := (⟨0, 1⟩ : ℂ),--(⟨(⟨0, 1⟩ : ℂ), by {simp,} ⟩ : ℍ),
  set F := pseries_of_holomorphic f (⟨i, by {simp only [zero_lt_one],} ⟩ : ℍ) with hF,
  have Fp : has_fpower_series_at (extend_by_zero f.val) F i := by {apply pseries_of_holomorphic_def},
  have rf := function_neq_zero_forall_z_pseries_neq_zero f hf_ne_zero,
  have tf : F ≠ 0 := rf (⟨i, by {simp only [zero_lt_one],} ⟩ : ℍ),
  set G := pseries_of_holomorphic g (⟨i, by {simp only [zero_lt_one],} ⟩ : ℍ) with hG,
  have Gp : has_fpower_series_at (extend_by_zero g.val) G i := by {apply pseries_of_holomorphic_def},
  have rg := function_neq_zero_forall_z_pseries_neq_zero g hg_ne_zero,
  have tg : G ≠ 0 := rg (⟨i, by {simp only [zero_lt_one],} ⟩ : ℍ),
  have ef := has_fpower_series_at.locally_ne_zero Fp tf,
  have eg := has_fpower_series_at.locally_ne_zero Gp tg,

  suffices : f.val * g.val ≠ 0,
  {
    simp only [subtype.val_eq_coe] at this,
    norm_cast at this,
  },
  suffices : extend_by_zero (f.val * g.val) ≠ 0,
    by exact extend_by_zero_f_neq_zero (f.val * g.val) this,

  rw extend_by_zero_mul,
  rcases ef with ⟨U, ⟨hU, ⟨V, ⟨hV,hfUV⟩⟩⟩⟩,
  rcases eg with ⟨U', ⟨hU', ⟨V', ⟨hV',hgUV'⟩⟩⟩⟩,
  simp only [filter.mem_principal, subtype.val_eq_coe, ne.def] at hfUV hgUV' hV hV',
  let W := V ∩ V',
  have hk : ∃ w, w ∈ (U ∩ U') ∩ W ∧ w ≠ i,
  {
    refine hkey i (U ∩ U') V V' _ hV hV',
    simp only [filter.inter_mem_iff],
    exact ⟨hU, hU'⟩,
  },
  simp only [subtype.val_eq_coe, ne.def],
  rcases hk with ⟨w, hwUW, hwi⟩,
  have hfw : extend_by_zero f.val w ≠ 0,
  {
    have : w ∈ U ∩ V  := ⟨hwUW.1.1, hwUW.2.1⟩,
    rw ← hfUV at this,
    simpa using this,
  },
  have hgw : extend_by_zero g.val w ≠ 0,
  {
    have : w ∈ U' ∩ V' := ⟨hwUW.1.2, hwUW.2.2⟩, 
    rw ← hgUV' at this,
    simpa using this,
  },
  have hfgw : (extend_by_zero f.val * extend_by_zero g.val) w ≠ 0,
  {
    change extend_by_zero f.val w * extend_by_zero g.val w ≠ 0,
    exact mul_ne_zero hfw hgw,
  },
  intro hc,
  apply hfgw,
  have hc' : (extend_by_zero ↑f * extend_by_zero ↑g) w = (0 : ℂ → ℂ) w,
  {
    rw hc,
  },
  simpa using hc,
end

-- Holℍ is an integral domain

instance : is_domain Holℍ := {
  mul_left_cancel_of_ne_zero := 
  begin
    intros f g h hyp1 hyp2,
    have : f*g - f*h = 0 := sub_eq_zero_of_eq hyp2,
    have : f * (g-h) = 0,
    {
      rw [mul_sub, this],
    },
    have : g - h = 0, from (Holℍ_eq_zero_or_eq_zero_of_mul_eq_zero f (g-h) this).resolve_left hyp1,
    exact eq_of_sub_eq_zero this,
  end,
  mul_right_cancel_of_ne_zero := 
  begin
    intros f g h hyp1 hyp2,
      have : f * g - h * g = 0 := sub_eq_zero_of_eq hyp2,
      have : (f - h) * g = 0,
      {
        rw [sub_mul, this],
      },
      have : f - h = 0, from (Holℍ_eq_zero_or_eq_zero_of_mul_eq_zero (f-h) g this).resolve_right hyp1,
      exact eq_of_sub_eq_zero this,
  end,
  exists_pair_ne :=
  begin
    use (λ z : ℍ', 0),
    split,
    exact zero_hol ℍ',
    exact const_is_bounded 0,
    use (λ z : ℍ', 1),
    split,
    exact one_hol ℍ',
    exact const_is_bounded 1,
    simp only [ne.def, subtype.mk_eq_mk, function.const_inj, zero_ne_one, not_false_iff],
  end }

lemma bounded_at_im_infty.smul {f : ℍ' → ℂ} (c : ℂ) (hf : is_bounded_at_im_infty f) : 
is_bounded_at_im_infty (λ z : ℍ, c * f z) :=
begin
let h : ℍ' → ℂ := λ z, c,
let j := const_is_bounded c,
exact is_bounded_at_im_infty.mul j hf,
end

instance : has_smul ℂ Holℍ := 
⟨λ r f, ⟨λ z, r * f.val z, ⟨smul_hol r f.val f.prop.diff,
bounded_at_im_infty.smul r f.prop.bdd_at_infty⟩⟩⟩

@[simp] lemma smul_def {f : ℍ' → ℂ} (hf : f ∈ Holℍ) {c : ℂ} : (c • f) = λ z, (c * (f z)) := rfl
@[simp] lemma smul_def' {f : Holℍ} {c : ℂ} : (c • f).val = λ z, (c * (f.val z)) := rfl

lemma comm_Holℍ (f g : Holℍ) : f*g = g*f :=
begin
apply subtype.eq,
simp [mul_comm],
end


instance : algebra ℂ Holℍ := 
{ smul := has_smul.smul,
  to_fun := λ r, ⟨(λ z, r), by {
    split,
    exact const_hol r,
    exact const_is_bounded r,
  }⟩,
  map_one':= rfl,
  map_mul':= λ _ _, rfl,
  map_zero' := rfl,
  map_add' := λ _ _, rfl,
  commutes' := λ _ _, by {rw comm_Holℍ},
  smul_def' := by {
    intros r f,
    simp,
    apply subtype.eq,
    simp,
    change _  = λ (z : ℍ'), r * f.val z,
    simp,
  }
}
