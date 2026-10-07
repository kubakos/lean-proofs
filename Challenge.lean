/-
Statement of record (Palomar Challenge) for the Erdős #1063 results in this repository.

The block from the module docstring "Erdős Problem 1063" to `end Erdos1063` is copied verbatim
from google-deepmind/formal-conjectures, `FormalConjectures/ErdosProblems/1063.lean` at commit
dbb5a21169ce4094913e6cad34faedd74df55157, except that FC's theorem
`erdos_1063.better_upper : let upper_bound : ℕ → ℝ := answer(sorry); …` is restated as the
definition `Statement (upper_bound : ℕ → ℝ) : Prop` (the same text as
`Research/Erdos1063/Statement.lean`, which `tools/fc_statement.py check` pins to FC). Comparator
requires `Erdos1063.n` and `Erdos1063.Statement` here to be identical to the Solution's. The
docstring on `Statement` is FC's docstring of `better_upper`. FC's other theorems in that file
(its solved variants and small values) are not copied. Copied text:
  Copyright 2026 The Formal Conjectures Authors.

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

  https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
-/
module

public import Mathlib

@[expose] public section

/-!
# Erdős Problem 1063

*References:*
 * [erdosproblems.com/1063](https://www.erdosproblems.com/1063)
 * [ErSe83] Erdos, P. and Selfridge, J. L., Problem 6447. Amer. Math. Monthly (1983), 710.
 * [Gu04] Guy, Richard K., _Unsolved problems in number theory_. (2004), Problem B31.
 * [Mo85] Monier, Jean-Marie, _Problems and Solutions: Solutions of Advanced Problems: 6447_.
   Amer. Math. Monthly **92** (1985), 435-436.
-/

open Filter Real
open scoped Nat Topology

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/--
Estimate $n_k$ by finding a better upper bound than Cambie's
$n_k \leq k \cdot \operatorname{lcm}(1, \dotsc, k-1)$.

The comparator takes its least common multiple in `ℕ` and casts the result. Writing the
ascription as `((… ).lcm (fun n : ℕ => n) : ℝ)` instead puts it on the `Finset.lcm`
application, so the coercion lands on `n` and the `lcm` is taken in `ℝ`, where `lcm` of
non-zero elements is `1` and the whole comparator collapses to `k`. -/
def Statement (upper_bound : ℕ → ℝ) : Prop :=
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
    upper_bound =o[atTop] fun k =>
      (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)

end Erdos1063

/-!
# The results

Erdős and Selfridge asked to estimate `n_k`, the least `n ≥ 2k` such that exactly one of
`n, n - 1, …, n - k + 1` fails to divide `C(n, k)`. Cambie observed `n_k ≤ k · lcm(1, …, k - 1)`,
which is `e^{(1 + o(1)) k}`; formal-conjectures' `erdos_1063.better_upper` (category
`research open` at the commit above) asks for an upper bound that is `o` of Cambie's.

Upper bounds:

* `better_upper` answers FC's `better_upper` with `2^⌊k/4⌋`: `n_k = O(2^⌊k/4⌋)`, and
  `2^⌊k/4⌋ = o(k · lcm(1, …, k - 1))`.
* `subexp_bound`: there is a constant `C` with `n_k ≤ exp(C · k · log log k / log k)` for all
  large `k`, the statement claimed (unreviewed) by P. White & Claude and by R. Cipollini;
  `n_le_exp_of_ge` gives `C = 100` for every `k ≥ 2^64`, and `exp_littleO` the consequence
  `n_k = exp(o(k))`. With `C = 100` this improves on Cambie's bound only for `k > 10^281`.

The structure of every admissible `m` (any `m ≥ 2k` with exactly one failing index `e`, not
only `m = n_k`), and a lower bound:

* `eq_mod_and_dvd`: `e = m mod k`, and `m - e` is divisible by
  `D(k, e) = ∏_{p^a ∥ k} p^(a + v_p(C(k-1, e)) + ⌊log_p max(e, k-1-e)⌋)`.
* `wheel`: for a prime `k/2 < p ≤ k`, if `p` divides only one of `m, …, m - k + 1` (that is,
  `m mod p + p ≥ k`), then that one is `m - e`.
* `lower_bound`: `n_k ≥ ∏_{p^a ∥ k} p^(a + ⌊log_p(k-1)⌋)`. It improves on `n_k ≥ 2k` only for
  composite `k ≠ 4`.

Here `p^a ∥ k` is written with `k.primeFactors` and `k.factorization`, `v_p` is
`Nat.factorization _ p`, and `⌊log_p x⌋` is `Nat.log p x`. Sources and credit are in
`formalization.yaml` and the README.
-/

namespace Erdos1063.Results

/-- FC's `erdos_1063.better_upper` with the answer `upper_bound k = 2^⌊k/4⌋`. -/
theorem better_upper : Statement (fun k => (2 : ℝ) ^ (k / 4)) := by
  sorry

/-- `n_k ≤ exp(C · k · log log k / log k)` for some constant `C` and all large `k`. -/
theorem subexp_bound :
    ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
      (n k : ℝ) ≤ Real.exp (C * k * Real.log (Real.log k) / Real.log k) := by
  sorry

/-- The same bound with `C = 100`, for every `k ≥ 2^64`. -/
theorem n_le_exp_of_ge {k : ℕ} (hk : 2 ^ 64 ≤ k) :
    (n k : ℝ) ≤ Real.exp (100 * k * Real.log (Real.log k) / Real.log k) := by
  sorry

/-- `n_k = exp(o(k))`: for every `ε > 0`, eventually `n_k ≤ exp(ε k)`. -/
theorem exp_littleO : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ Real.exp (ε * k) := by
  sorry

/-- If `m ≥ 2k` and `e` is the only index `i < k` with `(m - i) ∤ C(m, k)`, then `e = m mod k`
and `D(k, e) ∣ m - e`. -/
theorem eq_mod_and_dvd {m k e : ℕ} (h2k : 2 * k ≤ m) (hek : e < k)
    (hfail : ¬ (m - e) ∣ m.choose k)
    (hdiv : ∀ i < k, i ≠ e → (m - i) ∣ m.choose k) :
    e = m % k ∧
      (∏ q ∈ k.primeFactors,
        q ^ (k.factorization q + ((k - 1).choose e).factorization q +
          Nat.log q (max e (k - 1 - e)))) ∣ m - e := by
  sorry

/-- Under the same hypotheses, for a prime `k/2 < p ≤ k` with `m mod p + p ≥ k` (so `p` divides
exactly one of `m, …, m - k + 1`, namely `m - m mod p`), the failing index is `m mod p`. -/
theorem wheel {m k e p : ℕ} (h2k : 2 * k ≤ m) (hek : e < k)
    (hfail : ¬ (m - e) ∣ m.choose k)
    (hdiv : ∀ i < k, i ≠ e → (m - i) ∣ m.choose k)
    (hp : p.Prime) (hpk : p ≤ k) (hk2p : k < 2 * p) (hone : k ≤ m % p + p) :
    m % p = e := by
  sorry

/-- `n_k ≥ ∏_{p^a ∥ k} p^(a + ⌊log_p(k-1)⌋)` for every `k ≥ 2`. -/
theorem lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ q ∈ k.primeFactors, q ^ (k.factorization q + Nat.log q (k - 1)) ≤ n k := by
  sorry

end Erdos1063.Results
