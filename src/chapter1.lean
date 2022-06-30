import tactic
import linear_algebra.basis
import data.complex.basic
import data.polynomial.coeff

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
    simp only [int.cast_zero],
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

--exercise 1.7
example : ∃ U : set (ℝ × ℝ), (nonempty U ∧
  (∀ a : ℝ, ∀ u ∈ U, a•u ∈ U) ∧ 
  ¬(subspace' ℝ (ℝ × ℝ) U)) :=
begin
  use {v : ℝ × ℝ | ∃ x : ℝ, v = (0,x) ∨ v = (x,0)},
  split,
  { use [(0,0),0], --U is nonempty
    left,
    refl,
  },
  split,
  { rintros r u ⟨x, hx⟩, --U closed under scaling
    cases hx,
    { use r*x,
      left,
      simp [hx],},
    { use r*x,
      right,
      simp [hx],},
  },
  { rintros ⟨a, h, b⟩, clear a, clear b,        --but U not closed under addition
    specialize h (1,0) ⟨1,or.intro_right _ rfl⟩ --and is therefore not a subspace
                (0,1) ⟨1,or.intro_left _ rfl⟩,
    cases h with x hx,
    simp at hx,
    exact hx,
  }
end

--exercise 1.8
example (α : Type) (ι : α → set V) (H : ∀ a : α, subspace' F V (ι a)) :
        subspace' F V (⋂ a : α, ι a) :=
begin
  split,
  { rw set.mem_Inter,      --intersection contains 0
    exact λ a, (H a).1,},
  split,
  { intros u hu v hv,      --intersection closed under addition
    rw set.mem_Inter at *,
    exact λ a, (H a).2.1 u (hu a) v (hv a),},
  { intros r u hu,
    rw set.mem_Inter at *, --intersection closed under scaling
    exact λ a, (H a).2.2 r u (hu a),
  }
end

--exercise 1.9
example (U U' : set V) (hU : subspace' F V U) (hU' : subspace' F V U') :
  subspace' F V (U ∪ U') ↔ U ⊆ U' ∨ U' ⊆ U :=
begin
  split,
  { contrapose!,
    repeat {rw set.not_subset_iff_exists_mem_not_mem},
    rintros ⟨⟨x, hxU, hxU'⟩,⟨y, hyU', hyU⟩⟩ h,    --if neither subspace is a subset of the other,
    have hx : x ∈ U ∪ U',                         --we can choose x ∈ U \ U', y ∈ U' \ U
      {left, exact hxU},
    have hy : y ∈ U ∪ U',
      {right, exact hyU'},
    have hxy : x + y ∈ U ∪ U',                    --then x + y ∈ U ∪ U', since U ∪ U' subspace 
      {exact h.2.1 x hx y hy},
    cases hxy,
      { apply hyU,                                --but x + y ∈ U → y ∈ U, and x + y ∈ U' → x ∈ U'
        convert hU.2.1 ((-1)•x) (hU.2.2 (-1) x hxU) (x + y) (hxy),
        simp,},
      { apply hxU',
        convert hU'.2.1 ((-1)•y) (hU'.2.2 (-1) y hyU') (x + y) (hxy),
        simp,},
  },
  { intros h,
    cases h,
    { rw set.union_eq_self_of_subset_left h, --if U ⊆ U', then U ∪ U' = U' 
      exact hU'},                            --is a subspace
    { rw set.union_eq_self_of_subset_right h,
      exact hU},
  }
end

--exercise 1.10
example (U : set V) (hU : subspace' F V U) : {v | ∃ x y ∈ U, v = x + y} = U :=
begin
  ext a,
  split,
  { rintros ⟨x, hx, y, hy, rfl⟩,
    exact hU.2.1 x hx y hy,},
  { intro ha,
    use [a, ha, 0, hU.1],
    simp,}
end

--exercise 1.11, part i
example (U₁ U₂ : submodule F V) : U₁ ⊔ U₂ = U₂ ⊔ U₁ := sup_comm

--exercise 1.11, part ii
example (U₁ U₂ U₃ : submodule F V) : (U₁ ⊔ U₂) ⊔ U₃ = U₁ ⊔ (U₂ ⊔ U₃) := sup_assoc

--exercise 1.12, part i
example : ∃ U : submodule F V, ∀ U' : submodule F V, U ⊔ U' = U' :=
begin
  use ⊥,
  intro U',
  exact bot_sup_eq,
end

--exercise 1.12, part ii
example : ∀ U : submodule F V, (∃ U' : submodule F V, U ⊔ U' = ⊥) → U = ⊥ :=
begin
  rintros U ⟨U', hU'⟩,
  rw sup_eq_bot_iff at hU',
  exact hU'.left,
end

--exercise 1.13
example : ∃ U₁ U₂ W : submodule F (F × F), (U₁ ⊔ W = U₂ ⊔ W) ∧ (U₁ ≠ U₂) :=
begin
  use [⊥, ⊤, ⊤],
  simp,
  exact bot_ne_top,
end

section direct_sum
local notation U `⊕` W := U ⊔ W = ⊤ ∧ U ⊓ W = ⊥

--exercise 1.14
open polynomial
def U : subspace F (polynomial F) :=  --can these easy proofs be more automated?
{ carrier := {f | ∃ a b : F, f = a•X^2 + b•X^5},
  add_mem' :=
    begin
      rintro f g ⟨a,b,rfl⟩ ⟨c,d,rfl⟩,
      use [a+c,b+d],
      repeat {rw add_smul},
      ring,
    end,
  zero_mem' := ⟨0,0, by simp⟩,
  smul_mem' := 
    begin
      rintro c f ⟨a,b,rfl⟩,
      use [c*a, c*b],
      rw smul_add,
      repeat {rw mul_smul},
    end,}

def W : subspace F (polynomial F) :=
{ carrier := {f | f.coeff 2 = 0 ∧ f.coeff 5 = 0},
  add_mem' :=
    begin
      rintro f g ⟨hf2, hf5⟩ ⟨hg2, hg5⟩,
      split;
      rw coeff_add;
      simp *,
    end,
  zero_mem' := by simp,
  smul_mem' := 
    begin
      rintro c f ⟨hf2, hf5⟩,
      split;
      rw coeff_smul;
      simp *,
    end,}

--the actual problem. This was pretty painful
example : ∃ W : subspace F (polynomial F), (U F) ⊕ W :=
begin
  use W F,
  split,
  { ext,
    split,
    { exact λ _, by triv,},
    { intro a, clear a,
      let a := x.coeff 2,
      let b := x.coeff 5,
      let f := a•X^2 + b•X^5,
      let g := x - f,
      have hx : x = f + g := by simp,
      have hf : f ∈ (U F) := by use [a,b],
      have hg : g ∈ (W F),
      { split;
        simp [g, f, coeff_X_pow],},
      rw hx,
      exact submodule.add_mem_sup hf hg,
    }
  },
  { ext,
    split,
    { rintro ⟨hxU, hxW⟩,
      rcases hxU with ⟨a,b, hx⟩,
      have ha : a = x.coeff 2 := by simp [hx, coeff_X_pow],
      have hb : b = x.coeff 5 := by simp [hx, coeff_X_pow],
      cases hxW with hx1 hx2,
      rw [ha, hb, hx1, hx2] at hx,
      simp [hx],
    },
    { simp,
      rintro rfl,
      exact ⟨(U F).zero_mem, (W F).zero_mem⟩,},
  }
end

--exercise 1.15
def U₁ : submodule F (F × F) :=           --could also define U₁ as span {(1,0)}
{ carrier := {x | x.1 = 0},               --decided not to, since span isn't defined
  add_mem' := λ x y hx hy, by simp * at *,--until ch2
  zero_mem' := by simp,
  smul_mem' := λ c x hx, by simp * at *,
}

def U₂ : submodule F (F × F) :=
{ carrier := {x | x.2 = 0},
  add_mem' := λ x y hx hy, by simp * at *,
  zero_mem' := by simp,
  smul_mem' := λ c x hx, by simp * at *,
}

def W' : submodule F (F × F) :=
{ carrier := {x | x.1 = x.2},
  add_mem' := λ x y hx hy, by simp * at *,
  zero_mem' := by simp,
  smul_mem' := λ c x hx, by simp * at *,
}

example : ∃ U₁ U₂ W : subspace F (F × F), (U₁ ⊕ W) ∧ (U₂ ⊕ W) ∧ (U₁ ≠ U₂) :=
begin
  use [U₁ F, U₂ F, W' F],
  split,
  { split,
    { rw eq_top_iff,    --U₁ + W = V
      rintro ⟨a,b⟩ h, clear h,
      have h1 : ((0 : F), b-a) ∈ U₁ F := by simp [U₁],
      have h2 : (a, a) ∈ W' F := by simp [W'],
      convert submodule.add_mem_sup h1 h2;
      simp,},
    { rw eq_bot_iff,    --and U₁ ∩ W = 0
      rintro ⟨a,b⟩ h,
      simp [U₁, W'] at *,
      rw ←h.2,
      exact ⟨h.1,h.1⟩,
    },
  },
  split,
  { split,
    { rw eq_top_iff,    --U₂ + W = V
      rintro ⟨a,b⟩ h, clear h,
      have h1 : (a-b, (0 : F)) ∈ U₂ F := by simp [U₂],
      have h2 : (b, b) ∈ W' F := by simp [W'],
      convert submodule.add_mem_sup h1 h2;
      simp,},
    { rw eq_bot_iff,    --and U₂ ∩ W = 0
      rintro ⟨a,b⟩ h,
      simp [U₂, W'] at *,
      rw h.2,
      exact ⟨h.1,h.1⟩,},
  },
  { intro h,                --U₁ ≠ U₂ since (0,1) ∈ U₁ \ U₂
    let x : F × F := (0,1),
    have hx : x ∈ U₁ F := by simp [x, U₁],
    rw h at hx,
    simp [x, U₂] at hx,
    exact hx,
  }
end

end direct_sum