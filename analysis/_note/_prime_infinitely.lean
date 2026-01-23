import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorial.Basic
open Nat

theorem prime_infinitely_many : ∀ N, ∃ p ≥ N, Nat.Prime p :=
by
  -- Given N
  intro N

  let M := factorial N + 1
  let p := Nat.minFac M

  -- Use this p to show the existence of the proof
  use p

  have h1 : Nat.Prime p :=
  by

    -- minFac_prime: minFac m 是質數，當 m ≥ 2
    -- refine minFac_prime ?_ 的意思是
    -- 我要用 minFac_prime，但它還缺一個參數，先幫我留一個洞
    refine minFac_prime ?_

    -- Now the goal is "M ≥ 2"
    admit
    -- TODO: Prove M ≥ 2

  -- The goal now is "p ≥ N ∧ Nat.Prime p"
  constructor

  -- Here is to show that p ≥ N
  admit

  -- Here is to show p is prime
  exact h1

  -- admit



-- apply?
-- exact?
