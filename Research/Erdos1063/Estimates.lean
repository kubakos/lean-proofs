module

public import Research.Erdos1063.Construction

@[expose] public section

/-!
# Erdős 1063: size estimates for the construction (plan step 8)

* `Mmain_le`: `M ≤ k^(6e+4)`.
* `Qbox_le`: `Q ≤ ⌈k/e⌉^{|P|} · k^e`. Primes with `k % p ≥ 2e` contribute `⌈p/e⌉ ≤ ⌈k/e⌉`.
  The others are distinct primes, each dividing some `k - a` with `e < a < 2e`, so their
  product is at most `∏_{e<a<2e} (k - a) ≤ k^e`.
* `two_e_pow_card_le`: `(2e)^{|P|} ≤ 4^k`, because every `p ∈ P` exceeds `2e` and
  `∏_{p ∈ P} p ≤ k# ≤ 4^k`.
-/

namespace Erdos1063.Estimates

open Erdos1063.Construction Erdos1063.Box Nat Finset

variable {k e : ℕ}

theorem Qe_le (hek : e < k) : Qe k e ≤ k ^ (e + 1) := by
  unfold Qe
  rw [pow_succ']
  exact Nat.mul_le_mul_left k ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left (Nat.sub_le k 1) e))

theorem primeProd_le (h2e : 2 * e ≤ k) (hk : 0 < k) :
    ∏ q ∈ (range (2 * e + 1)).filter Nat.Prime, q ^ (Nat.log q k + 1) ≤ k ^ (2 * (2 * e + 1)) := by
  calc ∏ q ∈ (range (2 * e + 1)).filter Nat.Prime, q ^ (Nat.log q k + 1)
      ≤ ∏ q ∈ (range (2 * e + 1)).filter Nat.Prime, k ^ 2 := by
        refine prod_le_prod fun q hq => ?_
        obtain ⟨hqr, -⟩ := mem_filter.mp hq
        rw [pow_succ, sq]
        exact Nat.mul_le_mul (Nat.pow_log_le_self q hk.ne') (by have := mem_range.mp hqr; omega)
    _ = (k ^ 2) ^ #((range (2 * e + 1)).filter Nat.Prime) := prod_const _
    _ ≤ (k ^ 2) ^ (2 * e + 1) :=
        Nat.pow_le_pow_right (by positivity) ((card_filter_le _ _).trans (card_range _).le)
    _ = k ^ (2 * (2 * e + 1)) := by rw [← pow_mul]

theorem Mmain_le (hek : e < k) (h2e : 2 * e ≤ k) : Mmain k e ≤ k ^ (6 * e + 4) := by
  unfold Mmain
  calc Qe k e ^ 2 * ∏ q ∈ (range (2 * e + 1)).filter Nat.Prime, q ^ (Nat.log q k + 1)
      ≤ (k ^ (e + 1)) ^ 2 * k ^ (2 * (2 * e + 1)) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Qe_le hek) 2) (primeProd_le h2e (by omega))
    _ = k ^ (6 * e + 4) := by rw [← pow_mul, ← pow_add]; ring_nf

theorem ceilDiv_le_self {p h : ℕ} (hh : 1 ≤ h) : ceilDiv p h ≤ p := by
  unfold ceilDiv
  refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr ?_)
  rw [Nat.succ_mul]
  have := Nat.le_mul_of_pos_right p hh
  omega

theorem ceilDiv_mono {p q h : ℕ} (hpq : p ≤ q) : ceilDiv p h ≤ ceilDiv q h :=
  Nat.div_le_div_right (by omega)

theorem one_le_ceilDiv {k e : ℕ} (he : 1 ≤ e) (hek : e ≤ k) : 1 ≤ ceilDiv k e := by
  unfold ceilDiv
  exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)

theorem factor_le {p : ℕ} (hP : p ∈ Pset k e) (he : 1 ≤ e) (hek : e < k) :
    ceilDiv p (hfun k e p) ≤ if 2 * e ≤ k % p then ceilDiv k e else p := by
  have hlt := e_lt_mod hP hek
  obtain ⟨hpr, -, -, -⟩ := mem_filter.mp hP
  split_ifs with h
  · have : hfun k e p = e := by unfold hfun; omega
    rw [this]
    exact ceilDiv_mono (by have := mem_range.mp hpr; omega)
  · exact ceilDiv_le_self (by unfold hfun; omega)

theorem P2_prod_le (he : 1 ≤ e) (hek : e < k) (h2ek : 2 * e < k) :
    ∏ p ∈ (Pset k e).filter (fun p => ¬ 2 * e ≤ k % p), p ≤ k ^ e := by
  have hdvd : ∏ p ∈ (Pset k e).filter (fun p => ¬ 2 * e ≤ k % p), p ∣
      ∏ a ∈ Ioo e (2 * e), (k - a) := by
    refine Finset.prod_primes_dvd _ (fun p hp => ?_) (fun p hp => ?_)
    · exact (mem_filter.mp (mem_filter.mp hp).1).2.1.prime
    · obtain ⟨hP, h2⟩ := mem_filter.mp hp
      have hlt := e_lt_mod hP hek
      have hmem : k % p ∈ Ioo e (2 * e) := mem_Ioo.mpr ⟨hlt, by omega⟩
      refine dvd_trans ?_ (dvd_prod_of_mem _ hmem)
      exact ⟨k / p, by have := Nat.div_add_mod k p; omega⟩
  have hpos : 0 < ∏ a ∈ Ioo e (2 * e), (k - a) :=
    prod_pos fun a ha => by have := mem_Ioo.mp ha; omega
  calc _ ≤ ∏ a ∈ Ioo e (2 * e), (k - a) := Nat.le_of_dvd hpos hdvd
    _ ≤ ∏ _a ∈ Ioo e (2 * e), k :=
        prod_le_prod fun a _ => Nat.sub_le k a
    _ = k ^ #(Ioo e (2 * e)) := prod_const _
    _ ≤ k ^ e := Nat.pow_le_pow_right (by omega) (by simp; omega)

theorem Qbox_le (he : 1 ≤ e) (hek : e < k) (h2ek : 2 * e < k) :
    Qbox k e ≤ ceilDiv k e ^ #(Pset k e) * k ^ e := by
  unfold Qbox
  calc ∏ p ∈ Pset k e, ceilDiv p (hfun k e p)
      ≤ ∏ p ∈ Pset k e, (if 2 * e ≤ k % p then ceilDiv k e else p) :=
        prod_le_prod fun p hp => factor_le hp he hek
    _ = (∏ _p ∈ (Pset k e).filter (fun p => 2 * e ≤ k % p), ceilDiv k e) *
          ∏ p ∈ (Pset k e).filter (fun p => ¬ 2 * e ≤ k % p), p := prod_ite _ _
    _ ≤ ceilDiv k e ^ #(Pset k e) * k ^ e := by
        rw [prod_const]
        exact Nat.mul_le_mul (Nat.pow_le_pow_right (one_le_ceilDiv he hek.le) (card_filter_le _ _))
          (P2_prod_le he hek h2ek)

theorem two_e_pow_card_le : (2 * e) ^ #(Pset k e) ≤ 4 ^ k := by
  calc (2 * e) ^ #(Pset k e) = ∏ _p ∈ Pset k e, 2 * e := (prod_const _).symm
    _ ≤ ∏ p ∈ Pset k e, p :=
        prod_le_prod fun p hp => (mem_filter.mp hp).2.2.1.le
    _ ≤ ∏ p ∈ range (k + 1) with p.Prime, p := by
        refine prod_le_prod_of_subset_of_one_le (fun p hp => ?_) fun p hp _ => ?_
        · obtain ⟨hr, hpr, -⟩ := mem_filter.mp hp
          exact mem_filter.mpr ⟨hr, hpr⟩
        · exact (mem_filter.mp hp).2.one_lt.le
    _ ≤ 4 ^ k := primorial_le_four_pow k

end Erdos1063.Estimates
