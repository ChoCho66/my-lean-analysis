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

  -- goal: p ≥ N ∧ Nat.Prime p
  -- goal1: p ≥ N
  -- goal2: Nat.Prime p

  -- The poorf of goal1 will use goal2,
  -- we write goal2 as a lemma first
  have h_p_is_prime : Nat.Prime p := by

    -- minFac_prime: n >= 2 => n.minFac is prime
    -- refine minFac_prime ?_ 的意思是
    -- 我要用 minFac_prime，但它還缺一個參數，先幫我留一個洞
    refine minFac_prime ?_

    -- The goal now is "M != 1"

    have h_M_g_1 : M > 1 := by

      -- To show N! > 0
      have h_fact_N_g_0 : factorial N > 0 := by
        apply Nat.factorial_pos

      -- Nat.lt_add_of_pos_left: {k n : ℕ} (h : 0 < k) : n < k + n
      exact Nat.lt_add_of_pos_left h_fact_N_g_0

    -- Nat.ne_of_gt: a < b => a ≠ b
    have h_1_ne_M : 1 ≠ M := Nat.ne_of_lt h_M_g_1
    exact h_1_ne_M.symm

  -- Seperate the goal into two parts
  refine And.intro ?_ ?_

  -- To prove goal1: p ≥ N
  -- That is, minFac(N! + 1) ≥ N
  by_contra! contra_p_l_N

  have h_p_dvd_factN : p ∣ factorial N := by
    refine dvd_factorial ?_ ?_

    -- To show 0 < p
    apply Nat.minFac_pos M

    -- To show p <= N
    exact le_of_succ_le contra_p_l_N

  have h_p_dvd_M : p ∣ M := by
    simpa [p] using (Nat.minFac_dvd M)
  have h_devide_1 : p ∣ 1 := by
    have h_divide_sub : p ∣ M - factorial N := by
      exact Nat.dvd_sub h_p_dvd_M h_p_dvd_factN
      -- 把 M - factorial N 化簡成 1
    simpa [M, Nat.add_sub_cancel] using h_divide_sub
  have h_p_is_one : p = 1 := by
    exact eq_one_of_dvd_one h_devide_1

  exact h_p_is_prime.ne_one h_p_is_one

  -- To prove goal2: Nat.Prime p
  exact h_p_is_prime

-- The theorem prime_infinitely_many now is complete.












  -- have h_p_ge_2 : p ≥ 2 := by
  --   exact Prime.two_le h_p_is_prime
--   -- Here is to show p is prime
--   exact h_p_is_prime

--   -- admit



-- -- apply?
-- -- exact?
