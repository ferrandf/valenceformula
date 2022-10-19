import analysis.complex.cauchy_integral
import analysis.complex.upper_half_plane.topology
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.calculus.fderiv
import ring_theory.subsemiring.basic
import algebra.algebra.basic

open_locale classical
noncomputable theory

open_locale topological_space upper_half_plane
open complex set upper_half_plane

instance : has_coe (set ℍ) (set ℂ) := ⟨λ U, has_coe.coe '' U⟩

instance : has_coe (ℂ → ℂ) (ℍ → ℂ) := ⟨λ f, (λ z, f z)⟩

class is_holomorphic_on_ℍ (f : ℂ → ℂ) : Prop :=
  (diff : differentiable_on ℂ f (univ : set ℍ))
  (bdd_at_infty : is_bounded_at_im_infty (f : ℍ → ℂ))

lemma open_univ : is_open ((univ : set ℍ) : set ℂ) :=
  open_embedding.is_open_map open_embedding_coe _ is_open_univ


lemma analytic_of_holomorphic (f : ℂ → ℂ) [h : is_holomorphic_on_ℍ f] (z : ℍ) :
analytic_at ℂ f z :=
begin
  apply differentiable_on.analytic_at h.diff,
  refine mem_nhds_iff.mpr _,
  use (univ : set ℍ),
  exact ⟨rfl.subset, open_univ,
  (mem_image (λ (x : ℍ), has_coe.coe x) univ ↑z).mpr ⟨z, by finish⟩⟩,
end

def holoℍ := {f : ℂ → ℂ // is_holomorphic_on_ℍ f}

instance (f : holoℍ) : is_holomorphic_on_ℍ f.val := f.prop

variables (f : holoℍ) (z : ℍ)

def pseries_of_holomorphic := classical.some (analytic_of_holomorphic f.val z)

lemma pseries_of_holomorphic_def : has_fpower_series_at f.val (pseries_of_holomorphic f z) z :=
  (classical.some_spec (analytic_of_holomorphic f.val z))

lemma pseries_unique {z : ℍ} {p : formal_multilinear_series ℂ ℂ ℂ}
(hfp : has_fpower_series_at f.val p z) : p = pseries_of_holomorphic f z :=
begin
  apply has_fpower_series_at.eq_formal_multilinear_series hfp,
  apply pseries_of_holomorphic_def,
end

@[simp] def hol_order := (pseries_of_holomorphic f z).order

lemma hol_order_well_defined {p : formal_multilinear_series ℂ ℂ ℂ}
(hfp : has_fpower_series_at f.val p z) :  p.order = hol_order f z :=
  by simp [pseries_unique f hfp]


/-
structure meromorphic_function (F : ℂ → ℂ):=
  (f : ℂ → ℂ)
  (hf : is_holomorphic_on_ℍ f)
  (g : ℂ → ℂ)
  (hg : is_holomorphic_on_ℍ g)
  (quo : F = f / g)

-- def order (F : ℂ → ℂ) (h : meromorphic_function F) (z : ℍ) : ℤ :=
--  let ⟨f, hf, g, hg, quo⟩ := h in (@hol_order f hf z) - (@hol_order g hg z)
-/

lemma sum_of_bounded_is_bounded {f g : ℍ → ℂ} (hf : is_bounded_at_im_infty f)
  (hg : is_bounded_at_im_infty g) : is_bounded_at_im_infty (f + g) :=
  sorry


lemma const_is_bounded (c : ℂ) : is_bounded_at_im_infty (λ z : ℍ, c) :=
  begin
    sorry,
  end


def Holℍ : subsemiring (ℂ → ℂ) := {
  carrier := is_holomorphic_on_ℍ,
  mul_mem' := λ f g hf hg, ⟨differentiable_on.mul hf.diff hg.diff,
  prod_of_bounded_is_bounded hf.bdd_at_infty hg.bdd_at_infty⟩,
  one_mem' := ⟨differentiable_on_const 1, const_is_bounded 1⟩,
  /-begin
    split,
    exact differentiable_on_const 1,
    exact const_is_bounded 1,
  end,-/
  add_mem' := λ f g hf hg, ⟨differentiable_on.add hf.diff hg.diff,
  sum_of_bounded_is_bounded hf.bdd_at_infty hg.bdd_at_infty⟩,
  zero_mem' := ⟨differentiable_on_const 0, zero_form_is_bounded_at_im_infty⟩,
  /-
  begin
    split,
    exact differentiable_on_const 0,
    exact zero_form_is_bounded_at_im_infty,
  end
  -/
}

@[simp] lemma comm_Holℍ (f : Holℍ) (g : Holℍ) : f*g = g*f :=
sorry 


instance : algebra ℂ Holℍ := 
{ smul := 
  by {
    sorry,
  },
  to_fun := λ r, ⟨(λ z, r), by {
    split,
    exact differentiable_on_const r,
    exact const_is_bounded r,
  }⟩,
  map_one':= 
  by {
    refl,
  },
  map_mul':= by {
    intros x y,
    refl,
  },
  map_zero' := by {
    refl,
  },
  map_add' := by {
    intros x y,
    refl,
  },
  commutes' := by {
    intros r x,
    simp,
  },
  smul_def' := by {
    intros r x,
    simp,
    sorry,
  }
}