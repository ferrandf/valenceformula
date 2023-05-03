/-Included in the project Formalizing Modular Forms (Ferran Delgà Fernández)
under the supervision of Marc Masdeu.-/

import analysis.complex.upper_half_plane.topology
import analysis.complex.cauchy_integral
import analysis.complex.upper_half_plane.functions_bounded_at_infty
import analysis.calculus.fderiv
import algebra.algebra.basic
import ring_theory.subring.basic
import ring_theory.localization.fraction_ring
import upper_half_plane_manifold
import holomorphic_functions
import analysis.complex.basic
import analysis.analytic.isolated_zeros
import analysis.analytic.uniqueness
import algebra.ring.defs

/-
# Holomorphic and bounded at im_infty functions definition (is_holomorphic_bdd):

- We add a the bounded at im_infty property to our previously defined 
  is_holomorphic_on functions using results in 
  analysis.complex.upper_half_plane.functions_bounded_at_infty.

## Main definitions:

* class is_holomoprhic_bdd: sets the conditions any f : ℍ' → ℂ has to satisfy; 

* pseries_of_holomorphic: is the power series of a given is_holomorphic_bdd function;

* We define the order of a is_holomoprhic_bdd function at a given point.

## Main results:

* Any function thas satisfies is_holomorphic_bdd is also analytic using 
  its extension by zero (from file: holomorphic_functions.lean).

* The pseries_of_holomorphic is the formal_multilinear_series of the function.

* The order is well defined.

-/


open_locale classical
noncomputable theory

open_locale topological_space upper_half_plane
open complex set upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

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
  exact ⟨rfl.subset, open_univ, ⟨z, by tauto⟩⟩,
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

