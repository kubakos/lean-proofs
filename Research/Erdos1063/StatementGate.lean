module

public import Research.Erdos1063.Statement

@[expose] public section

/-!
# Erdős 1063, `better_upper`: statement gate, part A

* `statement_iff`: the FC statement with an existential over the answer `upper_bound` is
  equivalent to `nₖ = o(k · lcm(1..k−1))`. The answer witness carries no information beyond
  that asymptotic, so this is the claim to prove (witness: `n` itself).
* `n_two`, `n_three`, `n_four`: the `sInf` definition gives the values recorded in
  [Gu04] B31 (n₂ = 4, n₃ = 6, n₄ = 9), so `n` means "the least n ≥ 2k with exactly one
  failing index".

The statement gate checks that the formal statement says what the problem says. Part B,
non-triviality, is in `Existence.lean`: `two_mul_le_n` (the set defining `n k` is non-empty
for every k ≥ 2) and `not_isLittleO_self` (the false variant `nₖ = o(k)` is refuted).

    tools/check_axioms.sh Research.Erdos1063.StatementGate Erdos1063.Gate.statement_iff \
      Erdos1063.Gate.n_two Erdos1063.Gate.n_three Erdos1063.Gate.n_four
-/

namespace Erdos1063.Gate

open Erdos1063 Filter Asymptotics

/-- The comparison function of FC's statement: `k · lcm(1..k−1)` in `ℝ`. -/
noncomputable def cambie (k : ℕ) : ℝ := (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)

theorem statement_iff :
    (∃ ub, Statement ub) ↔ (fun k => (n k : ℝ)) =o[atTop] cambie := by
  constructor
  · rintro ⟨ub, h1, h2⟩
    exact h1.trans_isLittleO h2
  · intro h
    exact ⟨fun k => (n k : ℝ), isBigO_refl _ _, h⟩

theorem n_two : n 2 = 4 := by
  apply le_antisymm
  · exact Nat.sInf_le (by decide)
  · apply le_csInf ⟨4, by decide⟩
    rintro b hb
    have : 2 * 2 ≤ b := hb.1
    omega

theorem n_three : n 3 = 6 := by
  apply le_antisymm
  · exact Nat.sInf_le (by decide)
  · apply le_csInf ⟨6, by decide⟩
    rintro b hb
    have : 2 * 3 ≤ b := hb.1
    omega

/-- The only candidate below 9 is m = 8, where both 8 and 6 fail to divide C(8,4) = 70. -/
theorem n_four : n 4 = 9 := by
  apply le_antisymm
  · exact Nat.sInf_le (by decide)
  · apply le_csInf ⟨9, by decide⟩
    rintro b hb
    have hb8 : 8 ≤ b := by have := hb.1; omega
    by_contra! h
    interval_cases b
    exact absurd hb (by decide)

end Erdos1063.Gate
