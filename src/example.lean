import tactic -- imports all the Lean tactics
import linear_algebra.basis
import data.real.basic

-- Exercise 1 in chapter 2

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

-- Exercise 3 in chapter 2

#check linear_independent

-- example : ∃ t a b c : ℝ, a*(3,1,4) + b*(2,-3,5) + c*(5,9,t) = 0 ∧ (a,b,c) ≠ (0,0,0) :=
-- begin
--   sorry,
-- end
-- 
-- example ∃ t : ℝ, ¬ linear_independent ℝ