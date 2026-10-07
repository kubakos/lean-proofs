module

public import Research.Erdos1063.Statement
public import Research.Erdos1063.Local

@[expose] public section

/-!
# Erdős 1063: admissibility glue and a universal existence bound

* `mem_of_local`: if `m ≥ 2k`, some prime blocks index `e`, and no prime blocks any other
  index `i < k`, then `m` is admissible, so `n k ≤ m` (plan step 7's glue).
* `n_le_bigM`: for every `k ≥ 2`, `n k ≤ bigM k = k² · ∏_{p ≤ k} p^(⌊log_p k⌋ + 1)`. A crude
  existence bound, proved with exceptional index 0, stabilization for `p ≤ k` and `(G)`
  for `p > k`.
* `two_mul_le_n`: `2k ≤ n k` for every `k ≥ 2`, so the set in `n`'s definition is never empty.
* `not_isLittleO_self` (gate 3 part B): the false variant `nₖ = o(k)` is refuted. So FC's
  `better_upper` is not trivially true; together with `Gate.statement_iff` this settles the
  statement gate.
-/

namespace Erdos1063.Existence

open Erdos1063 Erdos1063.Local Nat Finset Filter Asymptotics

/-- The set whose infimum is `n k` (FC's definition, unfolded). -/
def admissible (k : ℕ) : Set ℕ :=
  {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧ ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

theorem n_eq (k : ℕ) : n k = sInf (admissible k) := rfl

theorem mem_of_local {m k e : ℕ} (h2k : 2 * k ≤ m) (hek : e < k)
    (hbad : ∃ p, p.Prime ∧ (m.choose k).factorization p < (m - e).factorization p)
    (hgood : ∀ p, p.Prime → ∀ i < k, i ≠ e →
      (m - i).factorization p ≤ (m.choose k).factorization p) :
    m ∈ admissible k := by
  have hkm : k ≤ m := by omega
  have hC : m.choose k ≠ 0 := Nat.pos_iff_ne_zero.mp (choose_pos hkm)
  refine ⟨h2k, e, hek, ?_, ?_⟩
  · obtain ⟨p, -, hlt⟩ := hbad
    intro hdvd
    have := (Nat.factorization_le_iff_dvd (by omega) hC).mpr hdvd p
    omega
  · intro i hi hie
    refine (Nat.factorization_le_iff_dvd (by omega) hC).mp fun p => ?_
    by_cases hp : p.Prime
    · exact hgood p hp i hi hie
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- `k² · ∏_{p ≤ k prime} p^(⌊log_p k⌋ + 1)`. -/
def bigM (k : ℕ) : ℕ := k ^ 2 * ∏ q ∈ (range (k + 1)).filter Nat.Prime, q ^ (Nat.log q k + 1)

theorem bigM_ne_zero {k : ℕ} (hk : k ≠ 0) : bigM k ≠ 0 := by
  unfold bigM
  refine mul_ne_zero (pow_ne_zero _ hk) (prod_ne_zero_iff.mpr fun q hq => ?_)
  exact pow_ne_zero _ (Nat.Prime.ne_zero (mem_filter.mp hq).2)

theorem factorization_bigM {p k : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    2 * k.factorization p + (Nat.log p k + 1) ≤ (bigM k).factorization p := by
  have hk : k ≠ 0 := by have := hp.two_le; omega
  rw [← hp.pow_dvd_iff_le_factorization (bigM_ne_zero hk), pow_add]
  unfold bigM
  refine mul_dvd_mul ?_ (dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩))
  rw [pow_mul, pow_right_comm]
  exact pow_dvd_pow_of_dvd (Nat.ordProj_dvd k p) 2

theorem le_bigM {k : ℕ} (hk : 2 ≤ k) : 2 * k ≤ bigM k := by
  have h1 : 1 ≤ ∏ q ∈ (range (k + 1)).filter Nat.Prime, q ^ (Nat.log q k + 1) :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun q hq =>
      pow_ne_zero _ (Nat.Prime.ne_zero (mem_filter.mp hq).2))
  unfold bigM
  nlinarith

/-- `v_p(d) ≤ log_p k` for `0 < d ≤ k`. -/
theorem factorization_le_log {p d k : ℕ} (hp : p.Prime) (hd : 0 < d) (hdk : d ≤ k) :
    d.factorization p ≤ Nat.log p k :=
  (Nat.le_log_of_pow_le hp.one_lt (Nat.ordProj_le p (by omega))).trans
    (Nat.log_mono_right hdk)

theorem bigM_mem {k : ℕ} (hk : 2 ≤ k) : bigM k ∈ admissible k := by
  set M := bigM k
  have hM : M ≠ 0 := bigM_ne_zero (by omega)
  have h2k : 2 * k ≤ M := le_bigM hk
  have hvM : ∀ p, p.Prime → p ≤ k →
      2 * k.factorization p + (Nat.log p k + 1) ≤ M.factorization p :=
    fun p hp hpk => factorization_bigM hp hpk
  -- stabilization for a prime p ≤ k, with e = 0 and N = M
  have hstab : ∀ p, p.Prime → p ≤ k →
      (M.choose k).factorization p + k.factorization p = M.factorization p := by
    intro p hp hpk
    have := stabilization (e := 0) (N := M) (k := k) hp (by omega) (by omega) hM fun d hd hdk =>
      (factorization_le_log hp hd hdk.le).trans_lt (by have := hvM p hp hpk; omega)
    simpa using this
  refine mem_of_local (e := 0) h2k (by omega) ?_ ?_
  · -- the smallest prime factor of k blocks index 0
    refine ⟨k.minFac, Nat.minFac_prime (by omega), ?_⟩
    have hp := Nat.minFac_prime (show k ≠ 1 by omega)
    have hpos : 0 < k.factorization k.minFac :=
      hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd k)
    have := hstab _ hp (Nat.minFac_le (by omega))
    simp only [Nat.sub_zero]
    omega
  · intro p hp i hi hi0
    rcases Nat.lt_or_ge k p with hkp | hpk
    · have := factorization_sub_le (p := p) (show k ≤ M by omega) hi
      rwa [Nat.factorization_factorial_eq_zero_of_lt hkp, add_zero] at this
    · have hiM : i < M := by omega
      have hvi : i.factorization p ≤ Nat.log p k := factorization_le_log hp (by omega) hi.le
      have hvMp := hvM p hp hpk
      rw [factorization_sub_eq_of_lt hp (by omega) hiM (by omega)]
      have := hstab p hp hpk
      omega

theorem n_le_bigM {k : ℕ} (hk : 2 ≤ k) : n k ≤ bigM k := Nat.sInf_le (bigM_mem hk)

theorem two_mul_le_n {k : ℕ} (hk : 2 ≤ k) : 2 * k ≤ n k :=
  (Nat.sInf_mem ⟨_, bigM_mem hk⟩ : n k ∈ admissible k).1

/-- **Gate 3 part B.** The false variant `nₖ = o(k)` is refuted. -/
theorem not_isLittleO_self :
    ¬ (fun k => (n k : ℝ)) =o[atTop] (fun k => (k : ℝ)) := by
  intro h
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((h.bound one_pos).and (eventually_ge_atTop 2))
  obtain ⟨hb, h2⟩ := hK (max K 2) (le_max_left _ _)
  have hn := two_mul_le_n (k := max K 2) (le_max_right _ _)
  simp only [Real.norm_natCast, one_mul] at hb
  have : (2 * max K 2 : ℝ) ≤ max K 2 := by exact_mod_cast hn.trans (by exact_mod_cast hb)
  have : (2 : ℝ) ≤ max K 2 := by exact_mod_cast h2
  linarith

end Erdos1063.Existence
