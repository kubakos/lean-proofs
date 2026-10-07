module

public import Research.Erdos1063.StatementGate
public import Mathlib.NumberTheory.Chebyshev

@[expose] public section

/-!
# Erdős 1063: from an exponential bound to FC's little-o (plan step 9)

* `cambie_ge`: FC's comparator `k · lcm(1..k-1)` is at least `2^(k-1)`, by Mathlib's
  `two_pow_le_mul_lcmUpto` and `Nat.lcmUpto n = (Icc 1 n).lcm id`.
* `isLittleO_of_pow_bound`: if eventually `n k ≤ 2^(k/4)`, then `nₖ = o(k · lcm(1..k-1))`.
-/

namespace Erdos1063.Asymptotic

open Erdos1063 Erdos1063.Gate Filter Asymptotics Chebyshev

theorem cambie_ge {k : ℕ} (hk : 1 ≤ k) : (2 : ℝ) ^ (k - 1) ≤ cambie k := by
  have h := two_pow_le_mul_lcmUpto (k - 1)
  rw [show k - 1 + 1 = k by omega] at h
  unfold cambie
  have : ((Finset.Icc 1 (k - 1)).lcm id : ℕ) = Nat.lcmUpto (k - 1) := rfl
  rw [this]
  exact_mod_cast h

theorem isLittleO_of_pow_bound (h : ∀ᶠ k in atTop, n k ≤ 2 ^ (k / 4)) :
    (fun k => (n k : ℝ)) =o[atTop] cambie := by
  refine IsLittleO.of_bound fun c hc => ?_
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (1 / c) (by norm_num : (1 : ℝ) < 2)
  filter_upwards [h, eventually_ge_atTop (4 * K + 8)] with k hk hkK
  have hcam := cambie_ge (k := k) (by omega)
  rw [Real.norm_natCast, Real.norm_of_nonneg ((by positivity : (0:ℝ) ≤ 2 ^ (k - 1)).trans hcam)]
  have hexp : k / 4 + K ≤ k - 1 := by omega
  have h1 : (n k : ℝ) ≤ 2 ^ (k / 4) := by exact_mod_cast hk
  have h2 : (2 : ℝ) ^ (k / 4) * 2 ^ K ≤ 2 ^ (k - 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) hexp
  have h3 : 1 ≤ c * 2 ^ K := by
    have := hK.le
    rw [div_le_iff₀ hc] at this
    linarith [mul_comm c ((2:ℝ) ^ K)]
  calc (n k : ℝ) ≤ 2 ^ (k / 4) := h1
    _ ≤ 2 ^ (k / 4) * (c * 2 ^ K) := le_mul_of_one_le_right (by positivity) h3
    _ = c * (2 ^ (k / 4) * 2 ^ K) := by ring
    _ ≤ c * 2 ^ (k - 1) := by gcongr
    _ ≤ c * cambie k := by gcongr

end Erdos1063.Asymptotic
