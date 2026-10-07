module

public import Research.Erdos1063.Main
public import Research.Erdos1063.Subexp
public import Research.Erdos1063.Structure

@[expose] public section

/-!
# Proofs of the statements in `Challenge.lean`

Each theorem restates its `Challenge.lean` counterpart, with the same name and type, and proves it
from the development in `Research/Erdos1063/`. Comparator checks that the types match, that
`Erdos1063.n` and `Erdos1063.Statement` are identical to the Challenge's, and that only
`propext`, `Classical.choice` and `Quot.sound` are used.
-/

open Filter Real
open scoped Nat Topology

namespace Erdos1063.Results

theorem better_upper : Statement (fun k => (2 : ℝ) ^ (k / 4)) :=
  Main.better_upper_explicit

theorem subexp_bound :
    ∃ C : ℝ, ∀ᶠ k : ℕ in atTop,
      (n k : ℝ) ≤ Real.exp (C * k * Real.log (Real.log k) / Real.log k) :=
  Subexp.subexp_bound

theorem n_le_exp_of_ge {k : ℕ} (hk : 2 ^ 64 ≤ k) :
    (n k : ℝ) ≤ Real.exp (100 * k * Real.log (Real.log k) / Real.log k) :=
  Subexp.n_le_exp_of_ge hk

theorem exp_littleO : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ Real.exp (ε * k) :=
  Subexp.exp_littleO

theorem eq_mod_and_dvd {m k e : ℕ} (h2k : 2 * k ≤ m) (hek : e < k)
    (hfail : ¬ (m - e) ∣ m.choose k)
    (hdiv : ∀ i < k, i ≠ e → (m - i) ∣ m.choose k) :
    e = m % k ∧
      (∏ q ∈ k.primeFactors,
        q ^ (k.factorization q + ((k - 1).choose e).factorization q +
          Nat.log q (max e (k - 1 - e)))) ∣ m - e :=
  ⟨Structure.eq_mod ⟨h2k, hek, hfail, hdiv⟩, Structure.D_dvd ⟨h2k, hek, hfail, hdiv⟩⟩

theorem wheel {m k e p : ℕ} (h2k : 2 * k ≤ m) (hek : e < k)
    (hfail : ¬ (m - e) ∣ m.choose k)
    (hdiv : ∀ i < k, i ≠ e → (m - i) ∣ m.choose k)
    (hp : p.Prime) (hpk : p ≤ k) (hk2p : k < 2 * p) (hone : k ≤ m % p + p) :
    m % p = e :=
  Structure.wheel ⟨h2k, hek, hfail, hdiv⟩ hp hpk hk2p hone

theorem lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ q ∈ k.primeFactors, q ^ (k.factorization q + Nat.log q (k - 1)) ≤ n k :=
  Structure.lower_bound hk

end Erdos1063.Results
