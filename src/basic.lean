import analysis.complex.cauchy_integral
import analysis.complex.upper_half_plane.topology
import analysis.complex.upper_half_plane.functions_bounded_at_infty

open_locale classical
noncomputable theory

open_locale topological_space upper_half_plane
open complex set upper_half_plane

instance : has_coe (set ℍ) (set ℂ) := ⟨λ U, has_coe.coe '' U⟩

@[simp] def is_holomorphic_on_ℍ (f : ℂ → ℂ) :=
  differentiable_on ℂ f (univ : set ℍ)

lemma open_univ : is_open ((univ : set ℍ) : set ℂ) :=
  open_embedding.is_open_map open_embedding_coe _ is_open_univ


lemma analytic_of_holomorphic (f : ℂ → ℂ) (h : is_holomorphic_on_ℍ f) (z : ℍ) : analytic_at ℂ f z :=
begin
  apply differentiable_on.analytic_at h,
  refine mem_nhds_iff.mpr _,
  use (univ : set ℍ),
  exact ⟨rfl.subset, open_univ,
  (mem_image (λ (x : ℍ), has_coe.coe x) univ ↑z).mpr ⟨z, by finish⟩⟩,
end

def pseries_of_holomorphic {f : ℂ → ℂ} (h : is_holomorphic_on_ℍ f) (z : ℍ) :=
  (classical.some (analytic_of_holomorphic f h z))

lemma pseries_of_holomorphic_def {f : ℂ → ℂ} (h : is_holomorphic_on_ℍ f) (z : ℍ)
: has_fpower_series_at f (pseries_of_holomorphic h z) z :=
  (classical.some_spec (analytic_of_holomorphic f h z))

lemma pseries_unique {f : ℂ → ℂ} (h : is_holomorphic_on_ℍ f) {z : ℍ}
{p : formal_multilinear_series ℂ ℂ ℂ}
(hfp : has_fpower_series_at f p z) : p = pseries_of_holomorphic h z :=
begin
  apply has_fpower_series_at.eq_formal_multilinear_series hfp,
  apply pseries_of_holomorphic_def,
end

@[simp] def hol_order {f : ℂ → ℂ} (h : is_holomorphic_on_ℍ f) (z : ℍ) : ℕ :=
  (pseries_of_holomorphic h z).order

lemma hol_order_well_defined {f : ℂ → ℂ} (h: is_holomorphic_on_ℍ f) {z : ℍ}
{p : formal_multilinear_series ℂ ℂ ℂ}
(hfp : has_fpower_series_at f p z) :  p.order = hol_order h z :=
  by simp [pseries_unique h hfp]

structure meromorphic_function (F : ℂ → ℂ):=
  (f : ℂ → ℂ)
  (g : ℂ → ℂ)
  (hf : is_holomorphic_on_ℍ f)
  (hg : is_holomorphic_on_ℍ g)
  (quo : F = f / g)

def order (F : ℂ → ℂ) (h : meromorphic_function F) (z : ℍ) : ℤ :=
  let ⟨f, g, hf, hg, quo⟩ := h in (hol_order hf z) - (hol_order hg z)





