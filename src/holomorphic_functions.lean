import analysis.complex.basic
import analysis.calculus.deriv
import tactic.pi_instances
import ring_theory.subring.basic
import analysis.normed_space.basic
import analysis.calculus.deriv
import analysis.analytic.basic



local attribute [instance] classical.prop_decidable
noncomputable theory

universes u v
open_locale classical topological_space big_operators filter
open filter complex asymptotics

-- Extend by zero definition and lemmas:

section
variables {α : Type*} {β : Type*} {s : set α}

def extend_by_zero [has_zero β] (f : s → β) : α → β :=
λ z, if h : z ∈ s then f ⟨z, h⟩ else 0

lemma extend_by_zero_eq_of_mem [has_zero β] (f : s → β) (x : α) (hx : x ∈ s):
  (extend_by_zero f) x = f ⟨ x, hx ⟩ :=
begin
  rw extend_by_zero, dsimp, split_ifs, tauto,
end

lemma extend_by_zero_zero [has_zero β] :
extend_by_zero (λ s, 0 : s → β) = (λ h, 0) :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_zero' [has_zero β] :
extend_by_zero (0 : s → β) = 0 :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]


lemma extend_by_zero_f_neq_zero [has_zero β] (f : s → β)
(h : extend_by_zero f ≠ 0) : f ≠ 0 :=
begin
contrapose! h,
rw h,
exact extend_by_zero_zero,
end

lemma extend_by_zero_f_eq_zero [has_zero β] (f : s → β)
(h : extend_by_zero f = 0) : f = 0 :=
begin

sorry,
end

lemma extend_by_zero_add [add_group β] (f g : s → β) :
extend_by_zero (f + g) = extend_by_zero f + extend_by_zero g :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_sum [add_comm_monoid β] (ι  : finset α) (F : ι →  s → β) :
extend_by_zero (λ (x : s), ∑ (i : ι ), F i x) = ∑ (i : ι), extend_by_zero (F i) :=
begin
ext z,
by_cases h : z ∈ s,
simp only [extend_by_zero, h, finset.sum_apply, dif_pos],
simp only [extend_by_zero, h, finset.sum_apply, dif_neg, not_false_iff, finset.sum_const_zero],
end

lemma extend_by_zero_mul [semiring β] (f g : s → β) :
extend_by_zero (f * g) = extend_by_zero f * extend_by_zero g :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_neg [add_group β] (f : s → β) :
extend_by_zero (-f) = -extend_by_zero f :=
by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

lemma extend_by_zero_smul [ring β] (c : β) (f : s → β) :
  extend_by_zero (c • f) = c • extend_by_zero f :=
  by ext z; by_cases h : z ∈ s; simp [extend_by_zero, h]

end

def open_subs := topological_space.opens ℂ

/--A function is Holomorphic on an open subset of the complex numbers, if for every point in the domain
there is a neibourhood around the point containing the derivative of the function. -/


def is_holomorphic_on {D : open_subs} (f : D.1 → ℂ) : Prop :=
  ∀ z : D.1, ∃ f', has_deriv_within_at (extend_by_zero f) (f') D.1 z


lemma is_holomorphic_on_iff_differentiable_on (D : open_subs) (f : D.1 → ℂ):
  differentiable_on ℂ (extend_by_zero f) D.1 ↔ is_holomorphic_on f:=
begin
  rw is_holomorphic_on,
  split,
  rw differentiable_on,
  intros hd z,
  have h1:= hd z.1 z.2,
  have h2:=  differentiable_within_at.has_fderiv_within_at h1,
  simp_rw has_deriv_within_at,
  simp_rw has_deriv_at_filter,
  simp_rw has_fderiv_within_at at h2,
  simp at *,
  dunfold fderiv_within at h2,
  dunfold differentiable_within_at at h1,
  rw dif_pos h1 at h2,
  use classical.some h1 1,
  simp,
  exact h2,
  intro hz,
  rw differentiable_on,
  intros x hx,
  have h1:= hz ⟨x, hx⟩,
  have h2:= classical.some_spec h1,
  apply has_deriv_within_at.differentiable_within_at  h2,
end

-- The last lemma enables us to work with either definition. We now know f being holomorphic on D
-- is the same as the extension by zero of f being differentiable on D.

variable {D : open_subs}

-- Extension by zero lemmas on open_subs:

lemma ext_by_zero_eq (D: open_subs) (c : ℂ):
∀ (y : ℂ), (y ∈ (D.1 : set ℂ)) → extend_by_zero (λ z : D.1, (c : ℂ)) y = c :=
begin
  intros y hy,
  rw extend_by_zero,
  simp only [dite_eq_ite],
  cases D,
  dsimp at *,
  simp only [ite_eq_left_iff] at *,
  intros A,
  solve_by_elim,
end

lemma ext_by_zero_eq_np (D: open_subs) (f : D.1 → ℂ) (y : ℂ) (h: y ∈ (D.1 : set ℂ)):
  extend_by_zero (f ) y = (f ⟨ y, h⟩) :=
begin
  rw extend_by_zero,
  simp,
  cases D,
  dsimp at *,
  exact dif_pos h,
end

lemma ext_by_zero_apply (D: open_subs) (f : D.1 → ℂ) (y : D.1) :
  extend_by_zero (f ) y = (f y) :=
begin
  have:= ext_by_zero_eq_np D f y y.2,
  rw this,
  simp,
end

-- The constant functions are holomorphic:

lemma const_hol  (c : ℂ) : is_holomorphic_on (λ z : D.1, (c : ℂ)) :=
begin
  rw is_holomorphic_on,
  intro z,
  use (0: ℂ),
  have h1:=has_deriv_within_at_const  z.1 D.1 c,
  have H:= has_deriv_within_at.congr_of_eventually_eq_of_mem h1 _ z.property ,
  convert H,
  rw  eventually_eq,
  rw eventually_iff_exists_mem,
  use D.1,
  have H2:= ext_by_zero_eq D c,
  split,
  have h3:= D.2,
  simp at h3,
  have h4:=is_open.mem_nhds h3 z.2,
  simp only [subtype.val_eq_coe],
  convert h4,
  simp,
  rw nhds_within,
  simp only [inf_eq_left, le_principal_iff],
  exact h4,
  exact H2,
end

lemma zero_hol (D: open_subs) : is_holomorphic_on (λ z : D.1, (0 : ℂ)) :=
begin
  apply const_hol (0 : ℂ),
end

lemma one_hol (D: open_subs) : is_holomorphic_on (λ z : D.1, (1 : ℂ)) :=
begin
apply const_hol (1 : ℂ),
end

-- Adding two holomorphic functions gives us another holomoprhic function:

lemma add_hol (f g : D.1 → ℂ) (hf : is_holomorphic_on f) (hg : is_holomorphic_on g) :
  is_holomorphic_on (f + g) :=
begin
  intro z,
  cases hf z with f'z Hf,
  cases hg z with g'z Hg,
  existsi (f'z + g'z),
  rw extend_by_zero_add,
  have := has_deriv_within_at.add Hf Hg,
  exact this,
end

-- Same for multiplication:

lemma mul_hol (f g : D.1 → ℂ) (hf : is_holomorphic_on f) (hg : is_holomorphic_on g) :
  is_holomorphic_on (f * g) :=
begin
  intro z,
  cases hf z with f'z Hf,
  cases hg z with g'z Hg,
  existsi f'z*(extend_by_zero g z) + (extend_by_zero f z) * g'z,
  rw extend_by_zero_mul,
  have := has_deriv_within_at.mul Hf Hg,
  exact this,
end

-- And for -f:

lemma neg_hol (f : D.1 → ℂ) (hf : is_holomorphic_on f) : is_holomorphic_on (-f) :=
begin
  intro z,
  cases hf z with f'z H,
  existsi -f'z,
  rw extend_by_zero_neg,
  have h3:=has_deriv_within_at.neg H,
  exact h3,
end

/--The ring of holomorphic functions-/
def hol_ring (D: open_subs) : subring (D.1 → ℂ) :=
{ carrier := {f : D.1 → ℂ | is_holomorphic_on f},
  zero_mem' := zero_hol D,
  add_mem'  := add_hol,
  neg_mem'  := neg_hol,
  mul_mem'  := mul_hol,
  one_mem'  := one_hol D
}

-- Given f a holomorphic function and c ∈ ℂ, c ⬝ f is also a holomoprhic function:

lemma smul_hol (c : ℂ) (f : D.1 → ℂ) (f_hol : is_holomorphic_on f) : is_holomorphic_on (c • f) :=
begin
  intro z₀,
  cases f_hol z₀ with f'z₀ Hf,
  existsi c * f'z₀,
  rw extend_by_zero_smul,
  have h2:= has_deriv_within_at.const_smul c Hf,
  exact h2,
end

def hol_submodule (D: open_subs) : submodule (ℂ)  (D.1 → ℂ) :=
{ carrier := {f : D.1 → ℂ | is_holomorphic_on f},
  zero_mem' := zero_hol D,
  add_mem' := add_hol,
  smul_mem' := smul_hol}
