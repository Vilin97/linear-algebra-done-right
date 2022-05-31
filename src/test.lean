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

example : ((-1 + (real.sqrt 3 : ℂ)*I)/2)^3 = 1 :=
begin
  have : (real.sqrt 3 : ℂ)^2 * I^2 = -3,
  { simp, exact_mod_cast @real.sq_sqrt 3 (by norm_num) },
  linear_combination (this, (-3+(real.sqrt(3)*I))/8),
end
