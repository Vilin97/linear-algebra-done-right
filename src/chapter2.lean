import tactic -- imports all the Lean tactics
import linear_algebra.basis
import data.real.basic
import data.complex.basic
import data.complex.module
import data.matrix.notation

variables (k : Type) (V : Type) [field k] [add_comm_group V] [module k V] 

lemma matrix.fin_tail_cons (α : Type) (n : ℕ) (w : α) (v : fin n → α) : fin.tail (matrix.vec_cons w v) = v :=
begin
  nth_rewrite 1 ← @fin.tail_cons _ (λ_,α) w v,
  refl,
end

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
  -- linear_combination (h.1, 1/2) (h.2, 1/2),
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

namespace exercise2A6

example (v1 v2 v3 v4: V) (lin_indep : linear_independent k ![v1, v2, v3, v4]) : linear_independent k ![v1-v2, v2-v3, v3-v4, v4] :=
begin
  rw fintype.linear_independent_iff at *,
  intros g h,
  let f := ![g 0, g 1 - g 0, g 2 - g 1, g 3 - g 2],
  specialize lin_indep f,
  suffices  hf : ∀ (i : fin 4), f i = 0,
  have g0 : g 0 = 0,
    calc g 0 = f 0 : rfl
        ...  = 0 : hf 0,
  have g1 : g 1 = 0,
    calc g 1 = g 1 - g 0 + g 0 : by ring
      ... = f 1 + g 0 : by refl
      ... = 0 : by rw [hf 1, g0, zero_add],
  have g2 : g 2 = 0,
    calc g 2 = g 2 - g 1 + g 1 : by ring
      ... = f 2 + g 1 : by refl
      ... = 0 : by rw [hf 2, g1, zero_add],
  have g3 : g 3 = 0,
    calc g 3 = g 3 - g 2 + g 2 : by ring
      ... = f 3 + g 2 : by refl
      ... = 0 : by rw [hf 3, g2, zero_add],
  
  intro i,
  fin_cases i,
  exact g0,
  exact g1,
  exact g2,
  exact g3,

  apply lin_indep,
  calc finset.univ.sum (λ (i : fin 4), f i • ![v1, v2, v3, v4] i) 
            = f 0 • v1 + f 1 • v2 + f 2 • v3 + f 3 • v4 : by 
            begin
              simp only [fin.sum_univ_succ, add_assoc, matrix.cons_val_zero, matrix.cons_val_succ, fin.succ_zero_eq_one, fin.succ_one_eq_two, fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk, fin.mk_zero, finset.sum_singleton, add_right_inj],
              refl,
            end
     ...    = g 0 • v1 + (g 1 - g 0) • v2 + (g 2 - g 1) • v3 + (g 3 - g 2) • v4 : rfl
     ...    = g 0 • (v1 - v2) + g 1 • (v2 - v3) + g 2 • (v3 - v4) + g 3 • v4 : by 
            begin
              simp only [smul_sub, sub_smul],
              abel,
            end
     ...    = finset.univ.sum (λ (i : fin 4), g i • ![v1 - v2, v2 - v3, v3 - v4, v4] i) : by
            begin
              simp only [fin.sum_univ_succ, add_assoc, matrix.cons_val_zero, matrix.cons_val_succ, fin.succ_zero_eq_one, fin.succ_one_eq_two, fintype.univ_of_subsingleton, fin.mk_eq_subtype_mk, fin.mk_zero, finset.sum_singleton, add_right_inj],
              refl,
            end
     ...    = 0 : h,
end

end exercise2A6

namespace exercise2A8

example (m : ℕ) (v : fin m → V) (lin_indep : linear_independent k v) (a : k) : a ≠ 0 → linear_independent k (λ i, (a : k) • v i) := 
begin
  rw fintype.linear_independent_iff at *,
  intros ha g h,
  specialize lin_indep (λ i, g i • a),
  simp only [←smul_smul, ha, algebra.id.smul_eq_mul, mul_eq_zero, or_false] at lin_indep,
  exact lin_indep h,
end

end exercise2A8

namespace exercise2A9

example (v w : V) (hw : w = -v) (hv : v ≠ (0:V)) : linear_independent k ![v] ∧ linear_independent k ![w] ∧ ¬ linear_independent k ![v+w] :=
begin
  split,
  simp only [linear_independent_unique, hv, matrix.cons_val_fin_one, ne.def, not_false_iff],
  split,
  rw hw,
  simp only [linear_independent_unique, hv, matrix.cons_val_fin_one, ne.def, neg_eq_zero, not_false_iff],
  rw [hw, add_right_neg],
  simp only [linear_independent_unique_iff, matrix.cons_val_fin_one, ne.def, eq_self_iff_true, not_true, not_false_iff],
end

end exercise2A9

namespace exercise2A10

example (m : ℕ) (v : fin m → V) (lin_indep : linear_independent k v) (w : V) (not_lin_indep : ¬ linear_independent k (v+(λ _, w))) : w ∈ submodule.span k (set.range v) := 
begin
  rw fintype.not_linear_independent_iff at not_lin_indep,
  cases not_lin_indep with g hg,
  simp only [pi.add_apply, smul_add, ne.def, finset.sum_add_distrib, ← finset.sum_smul] at hg,
  let G : k := finset.univ.sum g, -- TODO
  -- have G ≠ 0,
  
  sorry,
end

end exercise2A10

namespace exercise2A11
-- Exercise 2.A.11

example (n : ℕ) (v : fin n → V) (lin_indep : linear_independent k v) (w : V) : linear_independent k (matrix.vec_cons w v) ↔ w ∉ submodule.span k (set.range v)
:=
begin
  rw linear_independent_fin_succ,
  simp only [matrix.fin_tail_cons, lin_indep, matrix.cons_val_zero, true_and],
end

end exercise2A11