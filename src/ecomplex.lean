import analysis.complex.basic
import data.complex.basic
import order.bounded_order


/-!
# Extended complex numbers:

We define `ecomplex = ℂ∞ := with_top ℂ` to be the type of extended complex numbers,
We try to define some algebraic operations and a linear order on `ℂ∞`
and prove basic properties of these operations, conversions to/from `ℂ`.


## Main definitions

* `ℂ∞`: the extended complex numbers; defined as `with_top ℂ`; it is
  equipped with the following structures:

  - coercion from `ℂ` defined in the natural way;


* Coercions to/from other types:

  - coercion `ℂ → ℂ∞` is defined as `has_coe`, so one can use `(p : ℂ)` in a context that
    expects `z : ℂ∞`, and Lean will apply `coe` automatically;

  - `ecomplex.to_complex` sends `↑p` to `p` and `∞` to `0`;

  - `ecomplex.ne_top_equiv_complex` is an equivalence between `{z : ℂ∞ // z ≠ 0}` and `ℂ`.

## Implementation notes

We define a `can_lift ℂ∞ ℂ` instance, so one of the ways to prove theorems about an `ℂ∞`
number `z` is to consider the cases `z = ∞` and `z ≠ ∞`, and use the tactic `lift z to ℂ using hz`
in the second case. This instance is even more useful if one already has `hz : z ≠ ∞` in the
context, or if we have `(f : α → ℂ∞) (hf : ∀ z, f z ≠ ∞)`.

## Notations

* `C∞`: the type of the extended complex numbers;
* `ℂ`: the type of complex numbers; defined in `data.complex.basic`;
* `∞`: a localized notation in `ℂ∞` for `⊤ : ℂ∞`.



-/

open classical set
open_locale big_operators
noncomputable theory

variables {α : Type*} {β : Type*}

@[derive [has_zero, nontrivial, add_comm_monoid_with_one]]
def ecomplex := with_top ℂ

localized "notation `ℂ∞` := ecomplex" in ecomplex
localized "notation `∞` := (⊤ : ecomplex)" in ecomplex


namespace ecomplex

instance : inhabited ℂ∞ := ⟨0⟩

instance : has_top ℂ∞ := ⟨option.none⟩

instance : has_coe ℂ ℂ∞ := ⟨ option.some ⟩

instance can_lift : can_lift ℂ∞ ℂ (coe) (λ z, z ≠ ∞) :=
{ prf := λ x hx, ⟨option.get $ option.ne_none_iff_is_some.1 hx, option.some_get _⟩ }


lemma none_eq_top : (none : ecomplex) = ∞ := rfl
lemma some_eq_coe (z : ℂ) : (some z : ecomplex) = (↑z : ecomplex) := rfl

protected def to_complex : ecomplex → ℂ := with_top.untop' 0


end ecomplex