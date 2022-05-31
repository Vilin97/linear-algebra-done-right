import tactic -- imports all the Lean tactics
import linear_algebra.basis
import data.real.basic
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

-- approach 2
@[derive fintype] inductive ι : Type
| i1 : ι
| i2 : ι
| i3 : ι

def ind (t : ℝ) (i:ι) : ℝ × ℝ × ℝ :=
ι.cases_on i (3,1,4) (2,-3,5) (5,9,t)

example : ∃ t : ℝ, ¬ linear_independent ℝ (ind t) := 
begin
  use 2,
  rw fintype.not_linear_independent_iff,
  use (λ i, ι.cases_on i (3) (-2) (-1)),
  split,
  sorry,
  sorry,
end

--approach 3
def ind' (t : ℝ) :=
![![3,1,4], ![2,-3,5], ![5,9,t]]

example : ∃ t : ℝ, ¬ linear_independent ℝ (ind' t) :=
begin
  use 2,
  rw fintype.not_linear_independent_iff,
  use ![3, -2, -1],
  split,
  norm_num [fin.sum_univ_succ, ind'],
  use 0,
  norm_num,
end

#check ind 2 -- ind 2 : ι → ℝ × ℝ × ℝ
#check ind' 2 -- ind' 2 : fin 1.succ.succ → fin 1.succ.succ → ℝ
end exercise2A3

namespace exercise2A11
-- Exercise 2.A.11
variables (k : Type) (V : Type) [field k] [add_comm_group V] [module k V] 

example (n : ℕ) (v : fin n → V) (lin_indep : linear_independent k v) (w : V) : linear_independent k (matrix.vec_cons w v) ↔ w ∉ submodule.span k (set.range v)
:=
begin
  rw linear_independent_fin_succ,
  simp,
  
  

end

variables (n : ℕ) (α : Type) (v : fin n → α) (w : α)
#check matrix.vec_cons w v
#check fin.cons w v
#check fin.snoc v w


end exercise2A11