import .holh
import .ecomplex

/-
# Meromprohic functions definition:

- We define a meromorphic function as a quotient of two holomorphic and bounded
  at im_infty functions:

## Main definitions:

* Merℍ is the fraction ring of the previously defined Holℍ (file: holh.lean); 

* Merℍ.mk creates F = f/g from f ∈ Holℍ and g ∈ non_zero_divisors Holℍ;    

* Merℍ.numerator and Merℍ.denominator enables us to work with the original
  functions used to create F = f/g;

* Holℍ.zeros and Merℍ.zeros are the sets of points in ℍ such that its image 
  is zero;

* Merℍ.map is the function that maps z ∈ ℍ to F(z) = f(z)/g(z);

* tst' is the function that maps the poles of F to TOP (⊤) and the other points to F.map;

* We also define the order of a meromorphic function at a given point.

-/

open_locale classical
noncomputable theory

open_locale topological_space upper_half_plane
open complex set upper_half_plane

local notation `ℍ'`:=(⟨upper_half_space , upper_half_plane_is_open⟩: open_subs)

local notation `ℍ`:=upper_half_plane

variables (f : ℍ' → ℂ) [is_holomorphic_bdd f] (z : ℍ')

open localization

noncomputable def Merℍ := fraction_ring Holℍ

instance Merℍ_is_field : field Merℍ := 
begin
apply fraction_ring.field,
end

-- Create F = f/g

def Merℍ.mk (f : Holℍ) (g : non_zero_divisors Holℍ) : Merℍ := localization.mk f g

def Merℍ.numerator (F : Merℍ) : Holℍ :=
((monoid_of _).sec F).1

def Merℍ.denominator (F : Merℍ) : (non_zero_divisors Holℍ) :=
((monoid_of _).sec F).2

-- Zeros of a Holℍ or Merℍ function and poles of a Merℍ function.

def Holℍ.zeros (f : Holℍ) := f.val ⁻¹' ({0} : set ℂ)

def Merℍ.zeros (F : Merℍ) : set ℍ' := F.numerator.val ⁻¹' ({0} : set ℂ)

def poles (F : Merℍ) : set ℍ' := F.denominator.val.val ⁻¹' ({0} : set ℂ)

-- F(z) = f(z)/g(z):

def Merℍ.map (F : Merℍ) : ℍ' → ℂ := λ z, F.numerator.val z / (F.denominator.val.val z)

def tst' (F : Merℍ) : ℍ' → ecomplex := λ z, ite (z ∈ poles F) ⊤ ((F.map) z)

--Given F = f/g a meromorphic function and z ∈ ℍ, we can compute the order of F at z as
--the difference of the order of f and the order of g.

def Merℍ.order (F : Merℍ) (z : ℍ) : ℤ := 
Holℍ.order F.numerator z - Holℍ.order F.denominator z


