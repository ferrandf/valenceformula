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
  have hff := h.diff,
  have hf : differentiable_on ℂ (extend_by_zero f) (has_coe.coe '' (univ : set ℍ')),
  { 
    have j := (is_holomorphic_on_iff_differentiable_on ℍ' f),
    dsimp at j,
    rw ← mykey,
    exact iff.elim_right j hff,
  },
  apply differentiable_on.analytic_at hf,
  refine mem_nhds_iff.mpr _,
  use (univ : set ℍ'),
  exact ⟨rfl.subset, open_univ, ⟨z, by finish⟩⟩,
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
  prod_of_bounded_is_bounded hf.bdd_at_infty hg.bdd_at_infty⟩,
  one_mem' := ⟨one_hol ℍ', const_is_bounded 1⟩,
  add_mem' := λ f g hf hg, ⟨add_hol f g hf.diff hg.diff,
  hf.bdd_at_infty.add hg.bdd_at_infty⟩,
  zero_mem' := ⟨zero_hol ℍ', zero_form_is_bounded_at_im_infty⟩,
  neg_mem' := λ f hf, ⟨neg_hol f hf.diff,hf.bdd_at_infty.neg_left⟩
}

instance is_holomorphic_on' (f : Holℍ) : is_holomorphic_bdd f := sorry

def Holℍ.order (f : Holℍ) (z : ℍ) : ℤ := @hol_order f.val f.property z

constant x : ℍ'

instance : is_domain Holℍ := 
{ eq_zero_or_eq_zero_of_mul_eq_zero := 
  begin
  intros f g h,
  have hf := f.prop,
  have hff : is_holomorphic_bdd f.val := by assumption,
  --idea: f is holomorphic_bdd then it has_fpower_series_on_ball x r,
  --let's assume g≠0 for a neighbourhood of x, then f has to be zero in this neighbourhood.
  --if this happens, we have that the fpower series on ball near x is equal zero.
  --we can apply has_fpower_series_on_ball.eventually_eq_zero which says that if a 
  -- function f has fpower series equal to zero in a ball then the function is f == 0.
  --have p : formal_multilinear_series ℂ ℂ ℂ, sorry,
  by_contradiction,
  push_neg at h,
  cases h with hf_ne_zero hg_ne_zero,
  have hc : f * g ≠ 0,
  {
    set F := pseries_of_holomorphic f (⟨(⟨0, 1⟩ : ℂ), by sorry⟩ : ℍ') with hF,
    sorry
  },
  exact hc h,
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
exact prod_of_bounded_is_bounded j hf,
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

