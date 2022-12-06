import analysis.complex.upper_half_plane.topology
import analysis.complex.cauchy_integral
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.calculus.fderiv
import algebra.algebra.basic
import ring_theory.subring.basic
import ring_theory.localization.fraction_ring
import .upper_half_plane_manifold
import .holomorphic_functions
import analysis.complex.basic
import analysis.analytic.isolated_zeros
import analysis.analytic.uniqueness



open_locale classical
noncomputable theory

open_locale topological_space upper_half_plane
open complex set upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

--instance : has_coe (set ℍ) (set ℂ) := ⟨λ U, has_coe.coe '' U⟩

instance : has_coe (set ℍ') (set ℂ) := ⟨λ U, subtype.val '' U⟩

instance : has_coe (ℂ → ℂ) (ℍ → ℂ) := ⟨λ f, (λ z, f z)⟩

class is_holomorphic_bdd (f : ℍ' → ℂ) : Prop :=
  (diff : is_holomorphic_on f)
  (bdd_at_infty : is_bounded_at_im_infty f)

lemma open_univ : is_open ((univ : set ℍ') : set ℂ) :=
  open_embedding.is_open_map open_embedding_coe _ is_open_univ

lemma mykey' : (has_coe.coe : ℍ' → ℂ) = (λ z, z.val) :=
begin
  finish,
end

lemma mykey : upper_half_space = has_coe.coe '' (univ : set ℍ') :=
begin
  rw mykey',
  finish,
end

lemma analytic_of_holomorphic (f : ℍ' → ℂ) [h : is_holomorphic_bdd f] (z : ℍ') :
analytic_at ℂ (extend_by_zero f) z :=
begin
  have hf : differentiable_on ℂ (extend_by_zero f) (has_coe.coe '' (univ : set ℍ')),
  { 
    have j := (is_holomorphic_on_iff_differentiable_on ℍ' f),
    dsimp at j,
    rw ← mykey,
    exact iff.elim_right j h.diff,
  },
  apply differentiable_on.analytic_at hf,
  refine mem_nhds_iff.mpr _,
  use (univ : set ℍ'),
  exact ⟨rfl.subset, open_univ, sorry⟩,--⟨z, by finish⟩⟩,
end

lemma analytic_on_of_holomorphic (f : ℍ' → ℂ) [h : is_holomorphic_bdd f] : 
analytic_on ℂ (extend_by_zero f) ℍ' :=
begin
  have hf : differentiable_on ℂ (extend_by_zero f) (upper_half_space),
  { 
    have j := (is_holomorphic_on_iff_differentiable_on ℍ' f),
    dsimp at j,
    exact iff.elim_right j h.diff,
  },
  apply differentiable_on.analytic_on hf,
  exact upper_half_plane_is_open,
end

variables (f : ℍ' → ℂ) [is_holomorphic_bdd f] (z : ℍ')

noncomputable def pseries_of_holomorphic := classical.some (analytic_of_holomorphic f z)

lemma pseries_of_holomorphic_def : has_fpower_series_at (extend_by_zero f) (pseries_of_holomorphic f z) z :=
  (classical.some_spec (analytic_of_holomorphic f z))

lemma pseries_unique {z : ℍ} {p : formal_multilinear_series ℂ ℂ ℂ}
(hfp : has_fpower_series_at (extend_by_zero f) p z) : p = pseries_of_holomorphic f z :=
begin
  apply has_fpower_series_at.eq_formal_multilinear_series hfp,
  apply pseries_of_holomorphic_def,
end

@[simp] def hol_order : ℤ := (pseries_of_holomorphic f z).order

lemma hol_order_well_defined {p : formal_multilinear_series ℂ ℂ ℂ}
(hfp : has_fpower_series_at (extend_by_zero f) p z) :  (p.order : ℤ) = hol_order f z :=
  by simp [pseries_unique f hfp]

lemma const_is_bounded (c : ℂ) : is_bounded_at_im_infty (λ z : ℍ', c) :=
  begin
  simp only [bounded_mem],
  use c.abs, use 0,
  intros z hz,
  linarith,
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

lemma preconn_ℍ' : is_preconnected upper_half_space :=
begin
sorry,
end

lemma hol_bdd.eventually_eq_zero_everywhere (f : Holℍ) 
  (x : ℍ') (hF : ∀ᶠ z in 𝓝 x, (extend_by_zero f.val) z = 0):
  (extend_by_zero f.val) = (0 : ℂ → ℂ) :=
begin
have hf : analytic_on ℂ (extend_by_zero f.val) ℍ',
{
  --exact analytic_on_of_holomorphic f,
  sorry,
},
have tf : ∀ ⦃y⦄, y ∈ upper_half_space → (extend_by_zero f.val) y = (0 : ℂ → ℂ) y,
{
  exact analytic_on.eq_on_zero_of_preconnected_of_eventually_eq_zero hf preconn_ℍ' x.prop hF,
},


simp at tf,
simp,
sorry,
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

/-
@[simp] lemma eventually_mem_nhds {s : set α} {a : α} :
  (∀ᶠ x in 𝓝 a, s ∈ 𝓝 x) ↔ s ∈ 𝓝 a :=
eventually_eventually_nhds
-/

lemma hkey (z : ℂ) (U V V': set ℂ) (hU : U ∈ 𝓝 z) 
(hV : {z}ᶜ ⊆ V) (hV' : {z}ᶜ ⊆ V') : 
∃ (w : ℂ), w ∈ U ∩ (V ∩ V') ∧ w ≠ z :=
begin
have r : ∀ᶠ x in 𝓝 z, U ∈ 𝓝 x,
{
  rw eventually_mem_nhds,
  exact hU,
},

sorry,
end 

instance : is_domain Holℍ := 
{ eq_zero_or_eq_zero_of_mul_eq_zero := 
  begin
  intros f g q,
  by_contradiction,
  push_neg at h,
  cases h with hf_ne_zero hg_ne_zero,
  have hc : f * g ≠ 0,
  {
    let i := (⟨0, 1⟩ : ℂ),--(⟨(⟨0, 1⟩ : ℂ), by {simp,} ⟩ : ℍ),
    set F := pseries_of_holomorphic f (⟨i, by {simp,} ⟩ : ℍ) with hF,
    have Fp : has_fpower_series_at (extend_by_zero f.val) F i := by {apply pseries_of_holomorphic_def},
    have rf := function_neq_zero_forall_z_pseries_neq_zero f hf_ne_zero,
    have tf : F ≠ 0 := rf (⟨i, by {simp,} ⟩ : ℍ),
    set G := pseries_of_holomorphic g (⟨i, by {simp,} ⟩ : ℍ) with hG,
    have Gp : has_fpower_series_at (extend_by_zero g.val) G i := by {apply pseries_of_holomorphic_def},
    have rg := function_neq_zero_forall_z_pseries_neq_zero g hg_ne_zero,
    have tg : G ≠ 0 := rg (⟨i, by {simp,} ⟩ : ℍ),
    have ef := has_fpower_series_at.locally_ne_zero Fp tf,
    have eg := has_fpower_series_at.locally_ne_zero Gp tg,

    have aux1 : (extend_by_zero f.val) * (extend_by_zero g.val) ≠ 0,
    {
      rcases ef with ⟨U, ⟨hU, ⟨V, ⟨hV,hfUV⟩⟩⟩⟩,
      rcases eg with ⟨U', ⟨hU', ⟨V', ⟨hV',hgUV'⟩⟩⟩⟩,
      simp at hfUV hgUV' hV hV',
      let W := V ∩ V',
      have hk : ∃ w, w ∈ U ∩ W ∧ w ≠ i,
      {
        exact hkey i U V V' hU hV hV',
      },
      simp,
      rcases hk with ⟨w, hwUW, hwi⟩,
      have hfw : extend_by_zero f.val w ≠ 0,
      {
        have : w ∈ U ∩ V,
        {
          simp at hwUW,
          split,
          exact hwUW.1,
          exact hwUW.2.1,
        },
        rw ← hfUV at this,
        simpa using this,
      },
      have hgw : extend_by_zero g.val w ≠ 0,
      {
        have : w ∈ U' ∩ V',
        {
           
          sorry
        },
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
    },
    have aux2 : extend_by_zero (f.val * g.val) ≠ 0,
    {
      rw ← extend_by_zero_mul at aux1,
      exact aux1,
    },
    have aux3 : f.val * g.val ≠ 0,
    {
      exact extend_by_zero_f_neq_zero (f.val * g.val) aux2,
    },
    simp only [subtype.val_eq_coe] at aux3,
    norm_cast at aux3,
  },
  exact hc q,
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
  end
}


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


open localization

noncomputable def Merℍ := fraction_ring Holℍ

instance Merℍ_is_field : field Merℍ := 
begin
apply fraction_ring.field,
end

def Merℍ.mk (f : Holℍ) (g : non_zero_divisors Holℍ) : Merℍ := localization.mk f g

def Merℍ.numerator (F : Merℍ) : Holℍ :=
((monoid_of _).sec F).1

-- instance numerator_is_holomorphic (F : Merℍ) : is_holomorphic_on_ℍ F.numerator.val := F.numerator.property

def Merℍ.denominator (F : Merℍ) : (non_zero_divisors Holℍ) :=
((monoid_of _).sec F).2

--Given F = f/g a meromorphic function and z ∈ ℍ, we can compute the order of F at z as
--the difference of the order of f and the order of g.
def meromorphic.order (F : Merℍ) (z : ℍ) : ℤ := 
Holℍ.order F.numerator z - Holℍ.order F.denominator z

--next step would be to give the definition of a weakly modular form on the upper half plane.
--from here i could start by trying to state the valence formula.

