import tactic
import data.complex.basic

open complex

example : ((-1 + (real.sqrt 3 : ℂ)*I)/2)^3 = 1 :=
begin
  field_simp,
  ring_nf,
  norm_num,
  ring_nf,
  norm_cast,
  norm_num,
end

-- example : ((-1 + (real.sqrt 3 : ℂ)*I)/2)^3 = 1 :=
-- begin
--   have : (real.sqrt 3 : ℂ)^2 * I^2 = -3,
--   { simp, exact_mod_cast @real.sq_sqrt 3 (by norm_num) },
--   linear_combination (this, (-3+(real.sqrt(3)*I))/8),
-- end

variables (k : Type) (V : Type) [field k] [add_comm_group V] [module k V] 
variables (n : ℕ) (w : V)
-- variables (v : fin n → α)
-- #check matrix.vec_cons w v
-- #check fin.cons w v

variables (v : vector V n)
#check vector.cons w v
-- #check submodule.span k v
open complex
def myvec : vector ℂ 2 :=
⟨[1+I, 1-I], rfl⟩

example (g : fin 4 → k) (v0 v1 v2 v3 : V) : 
g 0 • v0 + (g 1 - g 0) • v1 + (g 2 - g 1) • v2 + (g 3 - g 2) • v3 = 
g 0 • (v0 - v1) + g 1 • (v1 - v2) + g 2 • (v2 - v3) + g 3 • v3 := sorry

example (f : fin 4 → k) (v0 v1 v2 v3 : V) : finset.univ.sum (λ (i : fin 4), f i • ![v0, v1, v2, v3] i) = f 0 • v0 + f 1 • v1 + f 2 • v2 + f 3 • v3 := sorry