module

public import Research.Erdos1063.Existence
public import Research.Erdos1063.Box

@[expose] public section

/-!
# Erdős 1063: the main construction is admissible (plan step 7)

For `1 ≤ e < k` with `k ≤ 4e²`, put `Q_e = k · C(k-1, e)`,
`M = Q_e² · ∏_{p ≤ 2e} p^(⌊log_p k⌋ + 1)`, `P = {p ≤ k prime : 2e < p, p ∤ Q_e}`,
`h_p = min(e, k % p - e)`, and `Q = ∏_{p ∈ P} ⌈p / h_p⌉`. Then `n k ≤ e + M · Q`
(`n_le_construction`). The construction is the claimed proof's (Cipollini / GPT-5.6 Sol)
with a simpler modulus.
-/

namespace Erdos1063.Construction

open Erdos1063 Erdos1063.Local Erdos1063.Existence Erdos1063.Box Nat Finset

variable {k e : ℕ}

def Qe (k e : ℕ) : ℕ := k * (k - 1).choose e

def Mmain (k e : ℕ) : ℕ :=
  Qe k e ^ 2 * ∏ q ∈ (range (2 * e + 1)).filter Nat.Prime, q ^ (Nat.log q k + 1)

def Pset (k e : ℕ) : Finset ℕ :=
  (range (k + 1)).filter fun p => p.Prime ∧ 2 * e < p ∧ ¬ p ∣ Qe k e

def hfun (k e p : ℕ) : ℕ := min e (k % p - e)

def Qbox (k e : ℕ) : ℕ := ∏ p ∈ Pset k e, ceilDiv p (hfun k e p)

theorem Qe_pos (hek : e < k) : 0 < Qe k e :=
  Nat.mul_pos (by omega) (choose_pos (by omega))

theorem k_le_Qe (hek : e < k) : k ≤ Qe k e :=
  Nat.le_mul_of_pos_right k (choose_pos (by omega))

theorem prod_pos' : 0 < ∏ q ∈ (range (2 * e + 1)).filter Nat.Prime, q ^ (Nat.log q k + 1) :=
  prod_pos fun q hq => pow_pos (Nat.Prime.pos (mem_filter.mp hq).2) _

theorem Mmain_pos (hek : e < k) : 0 < Mmain k e :=
  Nat.mul_pos (pow_pos (Qe_pos hek) 2) prod_pos'

theorem Qe_dvd_factorial (hek : e < k) : Qe k e ∣ k ! := by
  have h1 : k ! = k * (k - 1) ! := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [factorial_succ, show k - 1 + 1 = k by omega]
  rw [h1, Qe]
  refine mul_dvd_mul_left k (Dvd.intro (e ! * (k - 1 - e) !) ?_)
  rw [← mul_assoc, Nat.choose_mul_factorial_mul_factorial (by omega)]

/-- `v_p(M) ≥ 2 v_p(Q_e) + ⌊log_p k⌋ + 1` for primes `p ≤ 2e`. -/
theorem factorization_Mmain_small {p : ℕ} (hp : p.Prime) (hp2e : p ≤ 2 * e) (hek : e < k) :
    2 * (Qe k e).factorization p + (Nat.log p k + 1) ≤ (Mmain k e).factorization p := by
  rw [← hp.pow_dvd_iff_le_factorization (Mmain_pos hek).ne', pow_add]
  unfold Mmain
  refine mul_dvd_mul ?_ (dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩))
  rw [pow_mul, pow_right_comm]
  exact pow_dvd_pow_of_dvd (Nat.ordProj_dvd _ p) 2

/-- `v_p(M) ≥ 2 v_p(Q_e)` for every prime `p`. -/
theorem factorization_Mmain_Qe {p : ℕ} (hp : p.Prime) (hek : e < k) :
    2 * (Qe k e).factorization p ≤ (Mmain k e).factorization p := by
  rw [← hp.pow_dvd_iff_le_factorization (Mmain_pos hek).ne', pow_mul, pow_right_comm]
  unfold Mmain
  exact (pow_dvd_pow_of_dvd (Nat.ordProj_dvd _ p) 2).trans (dvd_mul_right _ _)

theorem log_le_one {p : ℕ} (hp : p.Prime) (h : k < p ^ 2) : Nat.log p k ≤ 1 := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · simp [hk0]
  · exact Nat.lt_succ_iff.mp (Nat.log_lt_of_lt_pow hk0.ne' h)

/-- Lucas, specialised: for `p ∈ P`, `e < k % p`. -/
theorem e_lt_mod {p : ℕ} (hP : p ∈ Pset k e) (hek : e < k) : e < k % p := by
  obtain ⟨-, hp, h2e, hndvd⟩ := mem_filter.mp hP
  exact lucas_mod_gt hp (by omega) hek (fun h => hndvd (dvd_mul_of_dvd_left h _))
    (fun h => hndvd (dvd_mul_of_dvd_right h _))

theorem n_le_construction (hk : 2 ≤ k) (he : 1 ≤ e) (hek : e < k) (hke : k ≤ 4 * e ^ 2) :
    n k ≤ e + Mmain k e * Qbox k e := by
  have hPpos : ∀ p ∈ Pset k e, 0 < p := fun p hP => (mem_filter.mp hP).2.1.pos
  have hhpos : ∀ p ∈ Pset k e, 0 < hfun k e p := fun p hP => by
    have := e_lt_mod hP hek
    unfold hfun; omega
  obtain ⟨t, ht1, htQ, hbox⟩ :=
    exists_small_multiple (Pset k e) hPpos (hfun k e) hhpos (Mmain k e)
  set M := Mmain k e with hMdef
  set Q := Qe k e with hQdef
  have hM : 0 < M := Mmain_pos hek
  set N := M * t with hNdef
  have hN : N ≠ 0 := Nat.mul_ne_zero hM.ne' (by omega)
  have hMN : ∀ p, p.Prime → M.factorization p ≤ N.factorization p := fun p _ =>
    (Nat.factorization_le_iff_dvd hM.ne' hN).mpr (dvd_mul_right M t) p
  have hQM : Q ^ 2 ≤ M := by
    rw [hMdef, Mmain]; exact Nat.le_mul_of_pos_right _ prod_pos'
  have h2k : 2 * k ≤ e + N := by
    have := k_le_Qe hek
    have : M ≤ N := Nat.le_mul_of_pos_right M (by omega)
    nlinarith
  have hkn : k ≤ e + N := by omega
  -- the primes handled by stabilization
  have hstabP : ∀ p, p.Prime → (p ≤ 2 * e ∨ p ∣ Q) →
      (∀ d, 0 < d → d < k → d.factorization p < N.factorization p) ∧
      Nat.log p k + Q.factorization p ≤ N.factorization p := by
    intro p hp hcase
    rcases hcase with hsmall | hdvd
    · have h1 : 2 * Q.factorization p + (Nat.log p k + 1) ≤ M.factorization p :=
          factorization_Mmain_small hp hsmall hek
      have h2 := hMN p hp
      refine ⟨fun d hd hdk => ?_, by omega⟩
      have := factorization_le_log hp hd hdk.le
      omega
    · by_cases hsmall : p ≤ 2 * e
      · have h1 : 2 * Q.factorization p + (Nat.log p k + 1) ≤ M.factorization p :=
          factorization_Mmain_small hp hsmall hek
        have h2 := hMN p hp
        refine ⟨fun d hd hdk => ?_, by omega⟩
        have := factorization_le_log hp hd hdk.le
        omega
      · have hpk : k < p ^ 2 := by nlinarith
        have hlog := log_le_one (k := k) hp hpk
        have hd1 : 1 ≤ Q.factorization p :=
          hp.factorization_pos_of_dvd (Qe_pos hek).ne' hdvd
        have h1 : 2 * Q.factorization p ≤ M.factorization p := factorization_Mmain_Qe hp hek
        have h2 := hMN p hp
        refine ⟨fun d hd hdk => ?_, by omega⟩
        have := factorization_le_log hp hd hdk.le
        omega
  have hT : ∀ p, p.Prime → (p ≤ 2 * e ∨ p ∣ Q) →
      ((e + N).choose k).factorization p + Q.factorization p = N.factorization p :=
    fun p hp hcase => stabilization hp hek hkn hN (hstabP p hp hcase).1
  refine (Nat.sInf_le (mem_of_local (e := e) h2k hek ?_ ?_)).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_left M htQ) e)
  · -- a prime factor of Q_e blocks index e
    have hQ2 : 2 ≤ Q := (show 2 ≤ k from hk).trans (k_le_Qe hek)
    have hp := Nat.minFac_prime (show Q ≠ 1 by omega)
    refine ⟨Q.minFac, hp, ?_⟩
    have hpos : 0 < Q.factorization Q.minFac :=
      hp.factorization_pos_of_dvd (by omega) (Nat.minFac_dvd Q)
    have := hT _ hp (Or.inr (Nat.minFac_dvd Q))
    rw [show e + N - e = N by omega]
    omega
  · intro p hp i hi hie
    rcases Nat.lt_or_ge k p with hkp | hpk
    · have := factorization_sub_le (p := p) hkn hi
      rwa [Nat.factorization_factorial_eq_zero_of_lt hkp, add_zero] at this
    · by_cases hcase : p ≤ 2 * e ∨ p ∣ Q
      · obtain ⟨hA, hlogQ⟩ := hstabP p hp hcase
        have hdist := dist_pos_lt hek hi hie
        rw [factorization_shift hp hek hkn hN hA hi hie]
        have := factorization_le_log hp hdist.1 hdist.2.le
        have := hT p hp hcase
        omega
      · -- p ∈ P: one carry
        push Not at hcase
        have hP : p ∈ Pset k e := mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hcase.1, hcase.2⟩
        have hpk2 : k < p ^ 2 := by nlinarith [hcase.1]
        have hlt := e_lt_mod hP hek
        have hep : e < p := by omega
        refine one_carry hp hkn hi hpk2 ?_
        have hz : N % p < hfun k e p ∨ p - N % p < hfun k e p := by
          rw [hNdef, mul_comm]; exact hbox p hP
        have hzp := Nat.mod_lt N hp.pos
        have hkp := Nat.mod_lt k hp.pos
        have hmod : (e + N) % p = (e + N % p) % p := by
          rw [Nat.add_mod, Nat.mod_eq_of_lt hep]
        rw [hmod]
        unfold hfun at hz
        rcases hz with hz | hz
        · have hz' : N % p < k % p - e := lt_of_lt_of_le hz (min_le_right _ _)
          rw [Nat.mod_eq_of_lt (by omega)]; omega
        · have hz' : p - N % p < e := lt_of_lt_of_le hz (min_le_left _ _)
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

end Erdos1063.Construction
