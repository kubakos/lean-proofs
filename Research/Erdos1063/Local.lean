module

public import Mathlib

@[expose] public section

/-!
# Erdős 1063: local divisibility lemmas

The p-adic toolkit for the construction (plan steps 1–3 and 5). The lemmas are adapted from
R. Cipollini's claimed proof, *An upper bound for Erdős–Selfridge Problem 1063* (2026,
unreviewed; <https://www.overleaf.com/read/hrpsqsnqktky>).

* `carry_iff`: Kummer's carry condition `m ≤ k % m + (n - k) % m` is `n % m < k % m`.
* `factorization_sub_le`: `v_p(n - i) ≤ v_p(C(n,k)) + v_p(k!)` for `i < k ≤ n`. In particular
  a prime `p > k` never blocks an index.
* `one_carry` (claim, Lemma 3): if `p² > k` and `n % p < k % p`, then `p` blocks no index.
* `lucas_mod_gt` (claim, §3): if `e < p`, `p ∤ k` and `p ∤ C(k-1, e)`, then `e < k % p`.
-/

namespace Erdos1063.Local

open Nat Finset

/-- Kummer's carry at modulus `m`: adding `k` and `n - k` carries exactly when
`n % m < k % m`. -/
theorem carry_iff {m n k : ℕ} (hm : 0 < m) (hkn : k ≤ n) :
    m ≤ k % m + (n - k) % m ↔ n % m < k % m := by
  have hn : n = k + (n - k) := (Nat.add_sub_cancel' hkn).symm
  have h1 := Nat.mod_lt k hm
  have h2 := Nat.mod_lt (n - k) hm
  have hsum : n % m = (k % m + (n - k) % m) % m := by
    conv_lhs => rw [hn]
    exact Nat.add_mod _ _ _
  constructor
  · intro h
    rw [hsum, Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega
  · intro h
    by_contra hlt
    push Not at hlt
    rw [hsum, Nat.mod_eq_of_lt hlt] at h
    omega

/-- The p-adic valuation of one factor `n - i` of `n (n-1) ⋯ (n-k+1) = k! · C(n,k)` is at most
`v_p(C(n,k)) + v_p(k!)`. -/
theorem factorization_sub_le {p n k i : ℕ} (hkn : k ≤ n) (hik : i < k) :
    (n - i).factorization p ≤ (n.choose k).factorization p + (k !).factorization p := by
  have hdesc : n.descFactorial k = k ! * n.choose k := descFactorial_eq_factorial_mul_choose n k
  have hprod : n.descFactorial k = ∏ j ∈ range k, (n - j) := descFactorial_eq_prod_range n k
  have hne : ∀ j ∈ range k, n - j ≠ 0 := fun j hj => by
    have := mem_range.mp hj; omega
  have hdvd : (n - i) ∣ k ! * n.choose k := by
    rw [← hdesc, hprod]
    exact dvd_prod_of_mem _ (mem_range.mpr hik)
  have hpos : k ! * n.choose k ≠ 0 := mul_ne_zero (factorial_ne_zero k)
    (Nat.pos_iff_ne_zero.mp (choose_pos hkn))
  have := (Nat.factorization_le_iff_dvd (hne i (mem_range.mpr hik)) hpos).mpr hdvd p
  rw [Nat.factorization_mul (factorial_ne_zero k) (Nat.pos_iff_ne_zero.mp (choose_pos hkn))]
    at this
  simpa [add_comm] using this

/-- **One carry** (claim, Lemma 3). If `p² > k` and adding `k` and `n - k` carries at the
first digit, then every factor `n - i` (`i < k`) has `v_p(n - i) ≤ v_p(C(n,k))`. -/
theorem one_carry {p n k i : ℕ} (hp : p.Prime) (hkn : k ≤ n) (hik : i < k) (hpk : k < p ^ 2)
    (hcarry : n % p < k % p) :
    (n - i).factorization p ≤ (n.choose k).factorization p := by
  set c := (n - i).factorization p with hc
  have hni : n - i ≠ 0 := by omega
  rcases Nat.eq_zero_or_pos c with h0 | hcpos
  · rw [h0]; exact Nat.zero_le _
  -- p ^ c ∣ n - i, so c ≤ log p n
  have hpc : p ^ c ∣ n - i := Nat.ordProj_dvd (n - i) p
  have hcle : c ≤ log p n := by
    apply Nat.le_log_of_pow_le hp.one_lt
    exact (Nat.le_of_dvd (by omega) hpc).trans (Nat.sub_le n i)
  rw [factorization_choose hp hkn (Nat.lt_succ_self (log p n))]
  -- every level a ∈ [1, c] carries
  have hsub : Ico 1 (c + 1) ⊆ {a ∈ Ico 1 (log p n + 1) | p ^ a ≤ k % p ^ a + (n - k) % p ^ a} := by
    intro a ha
    rw [mem_Ico] at ha
    rw [mem_filter, mem_Ico]
    refine ⟨⟨ha.1, by omega⟩, ?_⟩
    rw [carry_iff (pow_pos hp.pos a) hkn]
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · have : a = 1 := by omega
      subst this; simpa using hcarry
    · have hpa : k < p ^ a := lt_of_lt_of_le hpk (Nat.pow_le_pow_right hp.pos ha2)
      have hdvd : p ^ a ∣ n - i := (Nat.pow_dvd_pow p (by omega)).trans hpc
      have hni_mod : n % p ^ a = i := by
        obtain ⟨q, hq⟩ := hdvd
        rw [show n = i + p ^ a * q by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      rw [hni_mod, Nat.mod_eq_of_lt hpa]
      exact hik
  have := card_le_card hsub
  simpa using this

/-- **Lucas** (claim, §3). If `e < p`, `p ∤ k` and `p ∤ C(k-1, e)`, then `e < k % p`. -/
theorem lucas_mod_gt {p k e : ℕ} (hp : p.Prime) (hep : e < p) (hek : e < k)
    (hk : ¬ p ∣ k) (hc : ¬ p ∣ (k - 1).choose e) : e < k % p := by
  have := Fact.mk hp
  by_contra hle
  push Not at hle
  have ha : 0 < k % p := Nat.pos_of_ne_zero (fun h => hk (Nat.dvd_of_mod_eq_zero h))
  -- (k - 1) % p = k % p - 1 < e
  have hK : (k - 1) % p = k % p - 1 := by
    have hk1 : k = (k - 1) + 1 := by omega
    have : k % p = ((k - 1) % p + 1) % p := by
      conv_lhs => rw [hk1]
      exact Nat.add_mod _ _ _ |>.trans (by rw [Nat.mod_eq_of_lt hp.one_lt])
    have hlt : (k - 1) % p + 1 < p ∨ (k - 1) % p + 1 = p := by
      have := Nat.mod_lt (k - 1) hp.pos; omega
    rcases hlt with hlt | heq
    · rw [this, Nat.mod_eq_of_lt hlt]; omega
    · rw [this, heq, Nat.mod_self] at ha; omega
  have hlucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := k - 1) (k := e) (p := p)
  rw [Nat.mod_eq_of_lt hep, Nat.div_eq_of_lt hep, choose_zero_right, mul_one, hK,
    Nat.choose_eq_zero_of_lt (show k % p - 1 < e by omega)] at hlucas
  exact hc (Nat.modEq_zero_iff_dvd.mp hlucas)

/-! ### Stabilization (claim, Lemma 2) -/

theorem factorization_add_eq_of_lt {p x y : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x.factorization p < y.factorization p) :
    (x + y).factorization p = x.factorization p := by
  set c := x.factorization p
  have hxy : x + y ≠ 0 := by omega
  have h1 : p ^ c ∣ x := Nat.ordProj_dvd x p
  have h2 : ¬ p ^ (c + 1) ∣ x := Nat.pow_succ_factorization_not_dvd hx hp
  have h3 : p ^ (c + 1) ∣ y := (hp.pow_dvd_iff_le_factorization hy).mpr h
  have h4 : p ^ c ∣ x + y := dvd_add h1 ((Nat.pow_dvd_pow p (Nat.le_succ c)).trans h3)
  have h5 : ¬ p ^ (c + 1) ∣ x + y := fun hd => h2 ((Nat.dvd_add_left h3).mp hd)
  apply le_antisymm
  · by_contra hlt
    exact h5 ((hp.pow_dvd_iff_le_factorization hxy).mpr (by omega))
  · exact (hp.pow_dvd_iff_le_factorization hxy).mp h4

theorem factorization_sub_eq_of_lt {p x y : ℕ} (hp : p.Prime) (hx : x ≠ 0) (hxy : x < y)
    (h : x.factorization p < y.factorization p) :
    (y - x).factorization p = x.factorization p := by
  have hz : y - x ≠ 0 := by omega
  have hyz : x + (y - x) = y := by omega
  rcases lt_trichotomy ((y - x).factorization p) (x.factorization p) with hlt | heq | hgt
  · have := factorization_add_eq_of_lt hp hz hx hlt
    rw [add_comm, hyz] at this
    omega
  · exact heq
  · have := factorization_add_eq_of_lt hp hx hz hgt
    rw [hyz] at this
    omega

/-- `∏_{i < k, i ≠ e} |e - i| = e! · (k - 1 - e)!`. -/
theorem prod_dist_erase {e k : ℕ} (hek : e < k) :
    ∏ i ∈ (range k).erase e, Nat.dist e i = e ! * (k - 1 - e) ! := by
  induction k, hek using Nat.le_induction with
  | base =>
    rw [range_add_one, erase_insert (by simp), show e + 1 - 1 - e = 0 by omega, factorial_zero,
      mul_one, ← descFactorial_self, descFactorial_eq_prod_range]
    refine prod_congr rfl fun i hi => ?_
    have := mem_range.mp hi
    simp [Nat.dist, Nat.sub_eq_zero_of_le this.le]
  | succ k hk ih =>
    rw [range_add_one, erase_insert_of_ne (by omega), prod_insert (by simp), ih,
      show k + 1 - 1 - e = (k - 1 - e) + 1 by omega, factorial_succ]
    have : Nat.dist e k = k - 1 - e + 1 := by simp [Nat.dist]; omega
    rw [this]; ring

/-- The per-index part of stabilization, assuming only that the distances `|e - i|` have
smaller valuation than `N`: for `i ≠ e`, `v_p(e + N - i) = v_p(|e - i|)`. -/
theorem factorization_shift_of_dist {p e N k i : ℕ} (hp : p.Prime) (hek : e < k)
    (hkn : k ≤ e + N) (hN : N ≠ 0)
    (hA : ∀ i < k, i ≠ e → (Nat.dist e i).factorization p < N.factorization p) (hik : i < k)
    (hie : i ≠ e) :
    (e + N - i).factorization p = (Nat.dist e i).factorization p := by
  have hAi := hA i hik hie
  rcases lt_or_gt_of_ne hie with h | h
  · have hd : Nat.dist e i = e - i := by simp [Nat.dist]; omega
    rw [hd] at hAi ⊢
    rw [show e + N - i = (e - i) + N by omega]
    exact factorization_add_eq_of_lt hp (by omega) hN hAi
  · have hd : Nat.dist e i = i - e := by simp [Nat.dist]; omega
    rw [hd] at hAi ⊢
    rw [show e + N - i = N - (i - e) by omega]
    exact factorization_sub_eq_of_lt hp (by omega) (by omega) hAi

/-- **Stabilization**, assuming only that the distances `|e - i|` (`i < k`, `i ≠ e`) have
smaller valuation than `N`: then `v_p(C(e + N, k)) + v_p(k · C(k-1, e)) = v_p(N)`. -/
theorem stabilization_of_dist {p e N k : ℕ} (hp : p.Prime) (hek : e < k) (hkn : k ≤ e + N)
    (hN : N ≠ 0) (hA : ∀ i < k, i ≠ e → (Nat.dist e i).factorization p < N.factorization p) :
    ((e + N).choose k).factorization p + (k * (k - 1).choose e).factorization p =
      N.factorization p := by
  have hterm : ∀ i ∈ (range k).erase e,
      (e + N - i).factorization p = (Nat.dist e i).factorization p := by
    intro i hi
    obtain ⟨hie, hik⟩ := mem_erase.mp hi
    exact factorization_shift_of_dist hp hek hkn hN hA (mem_range.mp hik) hie
  have hdesc := descFactorial_eq_factorial_mul_choose (e + N) k
  rw [descFactorial_eq_prod_range] at hdesc
  have hne : ∀ i ∈ range k, e + N - i ≠ 0 := fun i hi => by have := mem_range.mp hi; omega
  have hsum : (∏ i ∈ range k, (e + N - i)).factorization p =
      N.factorization p + ∑ i ∈ (range k).erase e, (Nat.dist e i).factorization p := by
    rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply,
      ← Finset.add_sum_erase _ _ (mem_range.mpr hek), show e + N - e = N by omega]
    congr 1
    exact Finset.sum_congr rfl hterm
  have hdist : ∑ i ∈ (range k).erase e, (Nat.dist e i).factorization p =
      (e ! * (k - 1 - e) !).factorization p := by
    rw [← prod_dist_erase hek, Nat.factorization_prod, Finsupp.finsetSum_apply]
    intro i hi
    obtain ⟨hie, -⟩ := mem_erase.mp hi
    simp [Nat.dist]; omega
  have hfact : k ! = (k * (k - 1).choose e) * (e ! * (k - 1 - e) !) := by
    have h1 := Nat.choose_mul_factorial_mul_factorial (show e ≤ k - 1 by omega)
    have h2 : k ! = k * (k - 1) ! := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      rw [factorial_succ, show k - 1 + 1 = k by omega]
    rw [h2, ← h1, show k - 1 - e = k - 1 - e from rfl]; ring
  have hC : (e + N).choose k ≠ 0 := Nat.pos_iff_ne_zero.mp (choose_pos hkn)
  have hQ : k * (k - 1).choose e ≠ 0 :=
    mul_ne_zero (by omega) (Nat.pos_iff_ne_zero.mp (choose_pos (by omega)))
  have hF : e ! * (k - 1 - e) ! ≠ 0 := mul_ne_zero (factorial_ne_zero _) (factorial_ne_zero _)
  have key : (∏ i ∈ range k, (e + N - i)).factorization p =
      (k ! * (e + N).choose k).factorization p := by rw [hdesc]
  rw [hsum, hdist, hfact, Nat.factorization_mul (mul_ne_zero hQ hF) hC,
    Nat.factorization_mul hQ hF] at key
  simp only [Finsupp.coe_add, Pi.add_apply] at key
  omega

theorem dist_pos_lt {e i k : ℕ} (hek : e < k) (hik : i < k) (hie : i ≠ e) :
    0 < Nat.dist e i ∧ Nat.dist e i < k := by
  unfold Nat.dist; omega

/-- **Stabilization** (claim, Lemma 2). Write `n = e + N`. If every `0 < d < k` has
`v_p(d) < v_p(N)`, then `v_p(C(n, k)) + v_p(k · C(k-1, e)) = v_p(N)`. -/
theorem stabilization {p e N k : ℕ} (hp : p.Prime) (hek : e < k) (hkn : k ≤ e + N) (hN : N ≠ 0)
    (hA : ∀ d, 0 < d → d < k → d.factorization p < N.factorization p) :
    ((e + N).choose k).factorization p + (k * (k - 1).choose e).factorization p =
      N.factorization p :=
  stabilization_of_dist hp hek hkn hN fun i hik hie =>
    hA _ (dist_pos_lt hek hik hie).1 (dist_pos_lt hek hik hie).2

/-- The per-index part of stabilization: for `i ≠ e`, `v_p(e + N - i) = v_p(|e - i|)`. -/
theorem factorization_shift {p e N k i : ℕ} (hp : p.Prime) (hek : e < k) (hkn : k ≤ e + N) (hN : N ≠ 0)
    (hA : ∀ d, 0 < d → d < k → d.factorization p < N.factorization p) (hik : i < k)
    (hie : i ≠ e) :
    (e + N - i).factorization p = (Nat.dist e i).factorization p :=
  factorization_shift_of_dist hp hek hkn hN
    (fun j hjk hje => hA _ (dist_pos_lt hek hjk hje).1 (dist_pos_lt hek hjk hje).2) hik hie

end Erdos1063.Local
