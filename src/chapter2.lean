import tactic -- imports all the Lean tactics
import linear_algebra.basis
import data.real.basic
import data.complex.basic
import data.complex.module
import data.matrix.notation

-- Exercise 2.A.1

namespace exercise2A1

open submodule

lemma mem_pair_left {α : Type} {a b : α} {S : set α} (h : {a, b} ⊆ S) : a ∈ S := begin
  have ha : a ∈ {a,b} := set.mem_insert a {b},
  exact h ha,
end

lemma mem_pair_right {α : Type} {a b : α} {S : set α} (h : {a, b} ⊆ S) : b ∈ S := begin
  have hb : b ∈ {a,b},
    apply set.mem_insert_of_mem,
    exact set.mem_singleton b,
  exact h hb,
end

example (k : Type) (V : Type) [field k] [add_comm_group V] [module k V] (v1 v2 : V) : span k ({v1, v2} : set V) = span k ({v1-v2, v2} : set V) :=
begin
  ext,
  unfold span,
  split,
  simp only [set.mem_set_of_eq, mem_Inf],
  intros h p hp,
    apply h,
    intro v,
    intro hv,
    cases hv with h1 h2,
      rw h1,
      have k1 : (v1-v2) ∈ ↑p,
        exact mem_pair_left hp,
      have k2 : v2 ∈ ↑p,
        exact mem_pair_right hp,
      have k3 : (v1 - v2) + v2 = v1,
        simp only [sub_add_cancel],
      rw ← k3,
      exact p.add_mem k1 k2,
      
      rw set.mem_singleton_iff at h2,
      rw h2,
      exact mem_pair_right hp,

  simp only [set.mem_set_of_eq, mem_Inf],
  intros h p hp,
    apply h,
    intro v,
    intro hv,
    cases hv with h1 h2,
      rw h1,
      have k1 : v1 ∈ ↑p,
        exact mem_pair_left hp,
      have k2 : v2 ∈ ↑p,
        exact mem_pair_right hp,
      exact p.sub_mem k1 k2,
      
      rw set.mem_singleton_iff at h2,
      rw h2,
      exact mem_pair_right hp,
end

end exercise2A1

-- Exercise 2.A.3

namespace exercise2A3
-- approach 1
example : ∃ t a b c : ℝ, a • ((3,1,4) : ℝ × ℝ × ℝ) + b • (2,-3,5) + c • (5,9,t) = (0,0,0) ∧ (a,b,c) ≠ (0,0,0) :=
begin
  refine ⟨2, 3, -2, -1, _, by simp⟩,
  simp, split, ring, split, ring, ring,
end

--approach 2 (credit goes to Alex Best)
def ind' (t : ℝ) :=
![![3,1,4], ![2,-3,5], ![5,9,t]]

example : ∃ t : ℝ, ¬ linear_independent ℝ (ind' t) :=
begin
  unfold ind',
  use 2,
  rw fintype.not_linear_independent_iff,
  use ![3, -2, -1],
  split,
  norm_num [fin.sum_univ_succ, ind'],
  use 0,
  norm_num,
end

end exercise2A3

namespace exercise2A5
open complex 

example : linear_independent ℝ ![1+I, 1-I] :=
begin
  rw fintype.linear_independent_iff,
  intros g h i,
  simp [fin.sum_univ_succ, ext_iff] at h,
  have h1: g 0 + g 1 + (g 0 + - g 1) = 0+0,
    exact congr (congr_arg has_add.add h.left) h.right,
  have h2: g 0 + g 1 - (g 0 + - g 1) = 0-0,
    exact congr (congr_arg has_sub.sub h.left) h.right,
  ring_nf at h1,
  ring_nf at h2,
  fin_cases i,
  -- linear_combination 1/2*h.1 + 1/2*h.2 with {normalize := ff},
  linarith,
  linarith,
end

example : ¬ linear_independent ℂ ![1+I, 1-I] :=
begin
  rw fintype.not_linear_independent_iff,
  use ![-1,I],
  split,
  norm_num [fin.sum_univ_succ],
  ring_nf,
  simp only [I_sq, neg_neg, sub_self],
  use 0,
  simp only [matrix.cons_val_zero, ne.def, neg_eq_zero, one_ne_zero, not_false_iff],
end

end exercise2A5

namespace exercise2A11
-- Exercise 2.A.11
variables (k : Type) (V : Type) [field k] [add_comm_group V] [module k V] 

example (n : ℕ) (v : fin n → V) (lin_indep : linear_independent k v) (w : V) : linear_independent k (matrix.vec_cons w v) ↔ w ∉ submodule.span k (set.range v)
:=
begin
  rw linear_independent_fin_succ,
  have : fin.tail (matrix.vec_cons w v) = v,
  { nth_rewrite 1 ← @fin.tail_cons _ (λ_,V) w v,
  refl, },
  simp only [this, lin_indep, matrix.cons_val_zero, true_and],
end

end exercise2A11
