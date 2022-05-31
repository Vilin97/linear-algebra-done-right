import tactic
import linear_algebra.basis
import data.complex.basic

variables (F : Type) [field F] (V : Type) [add_comm_group V] [module F V]

section comp
open complex

--exercise 1.1
example (a b : ℝ) (h : a ≠ 0 ∨ b ≠ 0) : ∃ c d : ℝ,
  (1 : ℂ) / (a + b*I) = c + d*I :=
begin
  let z : ℂ := 1/(a + b*I),
  use [z.re, z.im],
  change z = z.re + z.im*I,
  exact (re_add_im z).symm,
end

--Thanks Alex Best for a much better proof of this!
--exercise 1.2
example : ((-1 + (real.sqrt 3 : ℂ)*I)/2)^3 = 1 :=
begin
  field_simp,
  ring_nf,
  norm_num,
  ring_nf,
  norm_cast,
  norm_num,
end

end comp
def subspace' (U : set V) :=
  ((0 : V) ∈ U) ∧
  (∀ u v ∈ U, u + v ∈ U) ∧ 
  (∀ a : F, ∀ u ∈ U, a•u ∈ U)

--exercise 1.3
example (v : V) : -(-v) = v := neg_neg v

--exercise 1.4
example (a : F) (v : V) (hav : a•v = 0) : a = 0 ∨ v = 0 := smul_eq_zero.mp hav

section ch1_ex5

--exercise 1.5a
example : @subspace' ℝ _ (ℝ × ℝ × ℝ) _ _
  {v : ℝ × ℝ × ℝ | ∃ x₁ x₂ x₃ : ℝ, v = (x₁, x₂, x₃) ∧ x₁ + 2*x₂ + 3*x₃ = 0} :=
begin
  split,
  { --contains 0
    exact ⟨0,0,0, rfl, by simp⟩},
  split,
  { --closed under addition
    rintros _ ⟨x₁, x₂, x₃, rfl, hxs⟩ _ ⟨y₁, y₂, y₃, rfl, hys⟩,
    use [x₁ + y₁, x₂ + y₂, x₃ + y₃],
    exact ⟨rfl, by linarith [hxs, hys]⟩,
  },
  { --closed under scaling
    rintros a _ ⟨x₁, x₂, x₃, rfl, hxs⟩,
    use [a*x₁, a*x₂, a*x₃],
    split,
    {refl,},
    calc --unfortunately, linarith can't solve this
      a * x₁ + 2 * (a * x₂) + 3 * (a * x₃) = a * (x₁ + 2 * x₂ + 3 * x₃) : by linarith
      ... = a * 0 : by rw hxs
      ... = 0 : mul_zero a,
  }
end

--exercise 1.5b
example : ¬ @subspace' ℝ _ (ℝ × ℝ × ℝ) _ _
  {v : ℝ × ℝ × ℝ | ∃ x₁ x₂ x₃ : ℝ, v = (x₁, x₂, x₃) ∧ x₁ + 2*x₂ + 3*x₃ = 4} :=
begin
  rintros ⟨a, h, b⟩, clear a, clear b, --this set is not closed under addition
  specialize h (4,0,0) ⟨4,0,0,rfl,by simp⟩ (4,0,0) ⟨4,0,0,rfl,by simp⟩,
  rcases h with ⟨x₁, x₂, x₃, h1, h⟩,
  simp * at *,
  rcases h1 with ⟨hx₁, hx₂, hx₃⟩,
  linarith,
end

--exercise 1.5c
example : ¬ @subspace' ℝ _ (ℝ × ℝ × ℝ) _ _
  {v : ℝ × ℝ × ℝ | ∃ x₁ x₂ x₃ : ℝ, v = (x₁, x₂, x₃) ∧ x₁*x₂*x₃ = 0} :=
begin
  rintros ⟨a, h, b⟩, clear a, clear b, --this set is not closed under addition
  specialize h (1,0,0) ⟨1,0,0,rfl,by simp⟩ (0,1,1) ⟨0,1,1,rfl,by simp⟩,
  rcases h with ⟨x₁, x₂, x₃, h1, h⟩,
  simp * at *,
  tidy,
end

--exercise 1.5d
example : subspace' ℝ (ℝ × ℝ × ℝ)
  {v : ℝ × ℝ × ℝ | ∃ x₁ x₂ x₃ : ℝ, v = (x₁, x₂, x₃) ∧ x₁ = 5*x₃} :=
begin
  split,
  { --contains 0
    exact ⟨0,0,0, rfl, by simp⟩},
  split,
  { --closed under addition
    rintros _ ⟨x₁, x₂, x₃, rfl, hxs⟩ _ ⟨y₁, y₂, y₃, rfl, hys⟩,
    use [x₁ + y₁, x₂ + y₂, x₃ + y₃],
    exact ⟨rfl, by linarith [hxs, hys]⟩,
  },
  { --closed under scaling
    rintros a _ ⟨x₁, x₂, x₃, rfl, hxs⟩,
    use [a*x₁, a*x₂, a*x₃],
    split,
    {refl,},
    rw hxs,
    rw [← mul_assoc, mul_comm a, mul_assoc],
  }
end

end ch1_ex5

--exercise 1.6
example : ∃ U : set (ℝ × ℝ), (nonempty U ∧
  (∀ u v ∈ U, u + v ∈ U) ∧
  (∀ u ∈ U, -u ∈ U) ∧ 
  ¬(subspace' ℝ (ℝ × ℝ) U)) :=
begin
  use {v : (ℝ × ℝ) | ∃ n m : ℤ, v = (n,m)},
  split,
  { use [(0,0),0,0], --U is nonempty
    refl,
  },
  split,
  { rintros _ ⟨n₁, n₂, rfl⟩ _ ⟨m₁, m₂, rfl⟩, --U closed under addition
    use [n₁ + m₁, n₂ + m₂],
    simp only [prod.mk_add_mk, int.cast_add],},
  split,
  { rintros _ ⟨n, m, rfl⟩, --U closed under negation
    use [-n, -m],
    simp only [prod.neg_mk, int.cast_neg],},
  { rintros ⟨a, b, h⟩, clear a, clear b,    --but U not closed under scaling
    specialize h (1/2) (1,0) ⟨1,0,by simp⟩, --and is therefore not a subspace
    rcases h with ⟨n, m, hnm⟩,
    rw prod.smul_mk at hnm,
    rw prod.mk.inj_iff at hnm,
    cases hnm with h a, clear a,
    field_simp at h,
    norm_cast at h,
    have h1 := odd_one,
    rw h at h1,
    rw int.odd_iff_not_even at h1,
    apply h1,
    simp,
    --probably a much better way to do this?
  }
end