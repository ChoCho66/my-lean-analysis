# 《Analysis I》 的 Lean 形式化

這個目錄中的檔案，包含我將著作 [_Analysis I_](https://terrytao.wordpress.com/books/analysis-i/) 以 [Lean](https://lean-lang.org/) 形式化的內容。此形式化力求忠實轉述原書，同時展示 Lean 的功能與語法；換句話說，並未為效率最佳化，在某些地方也可能偏離 Lean 的慣用寫法。

書中留給讀者的習題，在這份翻譯中會以 `sorry` 暫置。歡迎讀者 fork 這個儲存庫自行嘗試這些習題，不過我不打算直接把解答放在這裡。

雖然這份形式化在定義、定理與證明的安排上緊貼教材，我仍儘量避免直接引用書中內容，改為適時提供原文參考。因此這份形式化應視為原書的註解夥伴，而非替代品。

本書中的許多材料與 Lean 的標準數學函式庫 [Mathlib](https://leanprover-community.github.io/mathlib4_docs/) 有相同主題，但定義略有不同。為了調和差異，隨著內容深入，本形式化會逐步從教材自帶的定義過渡到 Mathlib 的定義，犧牲自包含性以換取與 Mathlib 的相容性。例如，第 2 章獨立於 Mathlib 建構自然數，但之後章節就會改用 Mathlib 的自然數。（第 2 章附錄中展示兩種自然數定義是同構的。）因此，本形式化也可以作為 Mathlib 各部分的入門。

為了符合 Mathlib 慣例，我對部分定義做了少量技術性調整，和原書版本略有不同，較重要者如下：

- 數列索引從 0 開始，而非 1，因為 Mathlib 對 0 起始的自然數 `ℕ` 支援較完整。
- 書中未定義的操作，例如除以零、對非柯西序列取形式極限，在這裡會賦予「雜湊值」（如 `0`），使運算完全定義。這是因為 Lean 對總函式的支援優於偏函式（濫用偏函式容易陷入「相依型態地獄」，連基本操作都需要細膩證明）。更多討論可參見 Kevin Buzzard 的[這篇部落格](https://xenaproject.wordpress.com/2020/07/05/division-by-zero-in-type-theory-a-faq/)。
- 第 2 章的自然數是用歸納型態建構，而非純公理化。不過皮亞諾公理已在[本章附錄](https://teorth.github.io/analysis/sec2e/)形式化。

## Sections

- _Chapter 1: Introduction (not formalized)_
- Chapter 2: Starting at the beginning: the natural numbers
  - Section 2.1: The Peano axioms ([Verso page](https://teorth.github.io/analysis/sec21/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_1.lean))
  - Section 2.2: Addition ([Verso page](https://teorth.github.io/analysis/sec22/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_2.lean))
  - Section 2.3: Multiplication ([Verso page](https://teorth.github.io/analysis/sec23/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_3.lean))
  - Chapter 2 epilogue: Isomorphism with the Mathlib natural numbers ([Verso page](https://teorth.github.io/analysis/sec2e/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_2_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_2_epilogue.lean))
- Chapter 3: Set theory
  - Section 3.1: Fundamentals ([Verso page](https://teorth.github.io/analysis/sec31/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_1.lean))
  - Section 3.2: Russell's paradox ([Verso page](https://teorth.github.io/analysis/sec32/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_2.lean))
  - Section 3.3: Functions ([Verso page](https://teorth.github.io/analysis/sec33/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_3.lean))
  - Section 3.4: Images and inverse images ([Verso page](https://teorth.github.io/analysis/sec34/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_4.lean))
  - Section 3.5: Cartesian products ([Verso page](https://teorth.github.io/analysis/sec35/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_5.lean))
  - Section 3.6: Cardinality of sets ([Verso page](https://teorth.github.io/analysis/sec36/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_6.lean))
  - Chapter 3 epilogue: Connections with ZFSet ([Verso page](https://teorth.github.io/analysis/sec3e/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_3_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_3_epilogue.lean))
- Chapter 4: Integers and rationals
  - Section 4.1: The integers ([Verso page](https://teorth.github.io/analysis/sec41/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_1.lean))
  - Section 4.2: The rationals ([Verso page](https://teorth.github.io/analysis/sec42/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_2.lean))
  - Section 4.3: Absolute value and exponentiation ([Verso page](https://teorth.github.io/analysis/sec43/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_3.lean))
  - Section 4.4: Gaps in the rational numbers ([Verso page](https://teorth.github.io/analysis/sec44/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_4_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_4_4.lean))
- Chapter 5: The Real numbers
  - Section 5.1: Cauchy sequences of rationals ([Verso page](https://teorth.github.io/analysis/sec51/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_1.lean))
  - Section 5.2: Equivalent Cauchy sequences ([Verso page](https://teorth.github.io/analysis/sec52/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_2.lean))
  - Section 5.3: Construction of the real numbers ([Verso page](https://teorth.github.io/analysis/sec53/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_3.lean))
  - Section 5.4: Ordering the reals ([Verso page](https://teorth.github.io/analysis/sec54/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_4.lean))
  - Section 5.5: The least upper bound property ([Verso page](https://teorth.github.io/analysis/sec55/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_5.lean))
  - Section 5.6: Real exponentiation, part I ([Verso page](https://teorth.github.io/analysis/sec56/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_6.lean))
  - Chapter 5 epilogue: Isomorphism with the Mathlib real numbers ([Verso page](https://teorth.github.io/analysis/sec5e/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_5_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_5_epilogue.lean))
- Chapter 6: Limits of sequences
  - Section 6.1: Convergence and limit laws ([Verso page](https://teorth.github.io/analysis/sec61/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_1.lean))
  - Section 6.2: The extended real number system ([Verso page](https://teorth.github.io/analysis/sec62/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_2.lean))
  - Section 6.3: Suprema and Infima of sequences ([Verso page](https://teorth.github.io/analysis/sec63/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_3.lean))
  - Section 6.4: Limsup, Liminf, and limit points ([Verso page](https://teorth.github.io/analysis/sec64/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_4.lean))
  - Section 6.5: Some standard limits ([Verso page](https://teorth.github.io/analysis/sec65/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_5.lean))
  - Section 6.6: Subsequences ([Verso page](https://teorth.github.io/analysis/sec66/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_6.lean))
  - Section 6.7: Real exponentiation, part II ([Verso page](https://teorth.github.io/analysis/sec67/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_7.lean))
  - Chapter 6 epilogue: Connections with Mathlib limits ([Verso page](https://teorth.github.io/analysis/sec6e/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_6_epilogue.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_6_epilogue.lean))
- Chapter 7: Series
  - Section 7.1: Finite series ([Verso page](https://teorth.github.io/analysis/sec71/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_1.lean))
  - Section 7.2: Infinite series ([Verso page](https://teorth.github.io/analysis/sec72/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_2.lean))
  - Section 7.3: Sums of non-negative numbers ([Verso page](https://teorth.github.io/analysis/sec73/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_3.lean))
  - Section 7.4: Rearrangement of series ([Verso page](https://teorth.github.io/analysis/sec74/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_4.lean))
  - Section 7.5: The root and ratio tests ([Verso page](https://teorth.github.io/analysis/sec75/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_7_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_7_5.lean))
- Chapter 8: Infinite sets
  - Section 8.1: Countability ([Verso page](https://teorth.github.io/analysis/sec81/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_8_1.lean))
  - Section 8.2: Summation on infinite sets ([Verso page](https://teorth.github.io/analysis/sec82/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_8_2.lean))
  - Section 8.3: Uncountable sets ([Verso page](https://teorth.github.io/analysis/sec83/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_8_3.lean))
  - Section 8.4: The axiom of choice ([Verso page](https://teorth.github.io/analysis/sec84/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_8_4.lean))
  - Section 8.5: Ordered sets ([Verso page](https://teorth.github.io/analysis/sec85/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_8_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_8_5.lean))
- Chapter 9: Continuous functions on `ℝ`
  - Section 9.1: Subsets of the real line ([Verso page](https://teorth.github.io/analysis/sec91/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_1.lean))
  - Section 9.2: The algebra of real-valued functions ([Verso page](https://teorth.github.io/analysis/sec92/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_2.lean))
  - Section 9.3: Limiting values of functions ([Verso page](https://teorth.github.io/analysis/sec93/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_3.lean))
  - Section 9.4: Continuous functions ([Verso page](https://teorth.github.io/analysis/sec94/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_4.lean))
  - Section 9.5: Left and right limits ([Verso page](https://teorth.github.io/analysis/sec95/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_5.lean))
  - Section 9.6: The maximum principle ([Verso page](https://teorth.github.io/analysis/sec96/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_6.lean))
  - Section 9.7: The intermediate value theorem ([Verso page](https://teorth.github.io/analysis/sec97/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_7.lean))
  - Section 9.8: Monotonic functions ([Verso page](https://teorth.github.io/analysis/sec98/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_8.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_8.lean))
  - Section 9.9: Uniform continuity ([Verso page](https://teorth.github.io/analysis/sec99/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_9.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_9.lean))
  - Section 9.10: Limits at infinity ([Verso page](https://teorth.github.io/analysis/sec910/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_9_10.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_9_10.lean))
- Chapter 10: Differentiation of functions
  - Section 10.1: Basic definitions ([Verso page](https://teorth.github.io/analysis/sec101/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_1.lean))
  - Section 10.2: Local maxima, local minima, and derivatives ([Verso page](https://teorth.github.io/analysis/sec102/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_2.lean))
  - Section 10.3: Monotone functions and derivatives ([Verso page](https://teorth.github.io/analysis/sec103/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_3.lean))
  - Section 10.4: Inverse functions and derivatives ([Verso page](https://teorth.github.io/analysis/sec104/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_4.lean))
  - Section 10.5: L'Hôpital's rule ([Verso page](https://teorth.github.io/analysis/sec105/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_10_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_10_5.lean))
- Chapter 11: The Riemann integral
  - Section 11.1: Partitions ([Verso page](https://teorth.github.io/analysis/sec111/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_1.lean))
  - Section 11.2: Piecewise constant functions ([Verso page](https://teorth.github.io/analysis/sec112/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_2.lean))
  - Section 11.3: Upper and lower Riemann integrals ([Verso page](https://teorth.github.io/analysis/sec113/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_3.lean))
  - Section 11.4: Basic properties of the Riemann integral ([Verso page](https://teorth.github.io/analysis/sec114/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_4.lean))
  - Section 11.5: Riemann integrability of continuous functions ([Verso page](https://teorth.github.io/analysis/sec115/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_5.lean))
  - Section 11.6: Riemann integrability of monotone functions ([Verso page](https://teorth.github.io/analysis/sec116/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_6.lean))
  - Section 11.7: A non-Riemann integrable function ([Verso page](https://teorth.github.io/analysis/sec117/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_7.lean))
  - Section 11.8: The Riemann-Stieltjes integral ([Verso page](https://teorth.github.io/analysis/sec118/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_8.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_8.lean))
  - Section 11.9: The two fundamental theorems of calculus ([Verso page](https://teorth.github.io/analysis/sec119/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_9.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_9.lean))
  - Section 11.10: Consequences of the fundamental theorem of calculus ([Verso page](https://teorth.github.io/analysis/sec1110/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Section_11_10.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Section_11_10.lean))
- Appendix A: The basics of mathematical logic
  - A.1: Mathematical statements ([Verso page](https://teorth.github.io/analysis/appA1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_1.lean))
  - A.2: Implication ([Verso page](https://teorth.github.io/analysis/appA2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_2.lean))
  - A.3: The structure of proofs ([Verso page](https://teorth.github.io/analysis/appA3/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_3.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_3.lean))
  - A.4: Variables and quantifiers ([Verso page](https://teorth.github.io/analysis/appA4/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_4.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_4.lean))
  - A.5: Nested quantifiers ([Verso page](https://teorth.github.io/analysis/appA5/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_5.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_5.lean))
  - A.6: Some examples of proofs and quantifiers ([Verso page](https://teorth.github.io/analysis/appA6/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_6.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_6.lean))
  - A.7: Equality ([Verso page](https://teorth.github.io/analysis/appA7/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_A_7.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_A_7.lean))
- Appendix B: The decimal system
  - B.1: The decimal representation of natural numbers ([Verso page](https://teorth.github.io/analysis/appB1/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_B_1.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_B_1.lean))
  - B.2: The decimal representation of real numbers ([Verso page](https://teorth.github.io/analysis/appB2/)) ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Appendix_B_2.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Appendix_B_2.lean))

## Additional content

我也利用這個儲存庫承載一些與教材無關的小型 Lean 內容：

- [我的測度論著作的形式化](https://github.com/teorth/analysis/tree/main/analysis/Analysis/MeasureTheory)（施工中）
- 物理單位的形式化
  - 單位系統的支援 ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/UnitsSystem.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/UnitsSystem.lean))
    - 使用範例 ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/UnitsSystemExamples.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/UnitsSystemExamples.lean))
  - SI 單位系統 ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/SI.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/SI.lean))
    - 使用範例 ([Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/SIExamples.html)) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/SIExamples.lean))
- 避免 Lean 選擇公理的有限選擇形式化
  - [Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/FiniteChoice.html) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/FiniteChoice.lean))
- 一些有限機率論 [Documentation](https://teorth.github.io/analysis/docs/Analysis/Misc/Probability.html) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/Probability.lean))
- [Erdos 問題 \#379 的解答](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_379.html) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/erdos_379.lean))
- [Pikhurko 對 Erdos 問題 \#613 的反例](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_613.html) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/erdos_613.lean))
- [Erdos 問題 \#707 的解答](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_707.html) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/erdos_707.lean))
- [Erdos 問題 \#987 的解答](https://teorth.github.io/analysis/docs/Analysis/Misc/erdos_987.html) ([Lean source](https://github.com/teorth/analysis/blob/main/analysis/Analysis/Misc/erdos_987.lean))

## Other resources

- [本專案網頁](https://teorth.github.io/analysis/)
  - [文件](https://teorth.github.io/analysis/docs/)
- [原書網頁](https://terrytao.wordpress.com/books/analysis-i/)
  - [Springer 版本](https://link.springer.com/book/10.1007/978-981-19-7261-4)
- [專案公告的部落格文章](https://terrytao.wordpress.com/2025/05/31/a-lean-companion-to-analysis-i/)，Terence Tao，2025/05/31。
- [Lean Zulip 上的討論串](https://leanprover.zulipchat.com/#narrow/channel/514017-Analysis-I)
- [貢獻者注意事項](./CONTRIBUTING.md)

## General Lean resources

- [Lean 社群](https://leanprover-community.github.io/)
  - [Lean4 線上 playground](https://live.lean-lang.org/)
  - [如何在本機跑 Lean 專案](https://leanprover-community.github.io/install/project.html)
  - [Lean 社群 Zulip 聊天](https://leanprover.zulipchat.com/)
  - [學習 Lean4](https://leanprover-community.github.io/learn.html)
    - [The natural number game](https://adam.math.hhu.de/)
    - [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - Jeremy Avigad 與 Patrick Massot 的 Lean 教科書
- [Mathlib 文件](https://leanprover-community.github.io/mathlib4_docs/)
  - [Mathlib 說明文件](https://seasawher.github.io/mathlib4-help/)
  - [Moogle](https://moogle-morphlabs.vercel.app/) - Mathlib 的語意搜尋引擎
  - [Loogle](https://loogle.lean-lang.org/) - Mathlib 的表達式比對搜尋引擎
  - [LeanSearch](https://leansearch.net/) - Mathlib 的自然語言搜尋引擎
  - [Mathlib tactic 列表](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)
    - [Lean tactic 小抄](https://github.com/fpvandoorn/LeanCourse24/blob/master/lean-tactics.pdf)
- Lean 擴充套件：
  - [Canonical](https://github.com/chasenorman/Canonical)
  - [Duper](https://github.com/leanprover-community/duper)
  - [LeanCopilot](https://github.com/lean-dojo/LeanCopilot)
- [常見 Lean 地雷](https://github.com/nielsvoss/lean-pitfalls)
- [Proof Stack Exchange 上的 Lean4 問答](https://proofassistants.stackexchange.com/questions/tagged/lean4)
- [The mechanics of proof](https://hrmacbeth.github.io/math2001/) - Heather Macbeth 的 Lean 入門教材
- [我的 Youtube 頻道](https://www.youtube.com/@TerenceTao27) 上有多種工具的 Lean 形式化示範。
- 更廣泛的 AI 與形式數學資源列表，可見[此文件](https://docs.google.com/document/d/1kD7H4E28656ua8jOGZ934nbH2HcBLyxcRgFDduH5iQ0)。

歡迎提供更多資源建議！

## Building

### 建置專案

安裝 [Lean](https://lean-lang.org/documentation/setup/) 並 clone 此儲存庫後，執行：

```
% ./build.sh
```

### 建置專案網頁

安裝 [Lean](https://lean-lang.org/documentation/setup/) 並 clone 此儲存庫後，執行：

```
% ./build-web.sh
```

完成後，`book/_site/` 會包含專案網頁。
可執行 `python3 serve.py` 將其作為網頁服務。

### 更新 Lean/Mathlib 版本

因為本專案使用已棄用的方式條件式引入 `doc-gen4`，
若要更新專案使用的 Lean 與 Mathlib 版本，請：
* 編輯 `analysis/lakefile.lean`，修改 Mathlib 與 doc-gen4 的 `require` 行以固定到下一版 Lean 的標籤（強烈建議逐版更新）
* 編輯 `analysis/lean-toolchain`，將 Lean 版本改成下一版
* 在 `analysis/` 中執行 `lake update -R -Kenv=dev`
* 這可能會把你的 `lean-toolchain` 設成最新的 Lean 版本；若發生，請改回預期版本

務必讓 `analysis/` 與 `book/` 目錄中對 `subverso` 的相依保持同步（特別是 `book/` 目錄使用的 toolchain 要一致）。
