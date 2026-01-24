import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Nat

theorem prime_infinitely_many : ∀ N, ∃ p ≥ N, Nat.Prime p := by
  -- Given N
  intro N

  let M := factorial N + 1
  let p := Nat.minFac M

  -- Use this p to show the existence of the proof
  use p

  have h_p_is_prime : Nat.Prime p := by

    -- The goal now is to show that p is prime

    -- minFac_prime: minFac m 是質數，當 m ≥ 2
    -- refine minFac_prime ?_ 的意思是
    -- 我要用 minFac_prime，但它還缺一個參數，先幫我留一個洞

    refine minFac_prime ?_
    -- The goal now is "M != 1"
    have h_M_g_1 : M > 1 := by

      have h_fact_N_g_0 : factorial N ≥ 1 := by
        apply Nat.factorial_pos

      apply?

    -- Nat.ne_of_gt: a < b => a ≠ b
    have h_1_ne_M : 1 ≠ M := Nat.ne_of_lt h_M_g_1
    exact h_1_ne_M.symm

  -- The goal now is "p ≥ N ∧ Nat.Prime p"
  constructor

  -- Here is to show that p ≥ N
  apply?

  -- Here is to show p is prime
  exact h_p_is_prime

  -- admit



-- apply?
-- exact?
