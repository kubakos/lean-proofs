/-
`erdos_1063.better_upper`, transcribed verbatim from google-deepmind/formal-conjectures
by tools/fc_statement.py (ADR 0002). Generated file: do not edit. Regenerate with
  .venv/bin/python tools/fc_statement.py render FormalConjectures/ErdosProblems/1063.lean erdos_1063.better_upper --sha dbb5a21169ce4094913e6cad34faedd74df55157

fc-sha: dbb5a21169ce4094913e6cad34faedd74df55157
fc-path: FormalConjectures/ErdosProblems/1063.lean
fc-theorem: erdos_1063.better_upper
fc-category: research open
fc-shape: let

Everything after `@[expose] public section` is copied from that file at that commit, except
the line `def Statement (upper_bound : ℕ → ℝ) : Prop :=` and the closing `end` lines. A claim about this problem is
`Erdos1063.Statement` or its negation. Copied text:
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

def Statement (upper_bound : ℕ → ℝ) : Prop :=
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
    upper_bound =o[atTop] fun k =>
      (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)

end Erdos1063
