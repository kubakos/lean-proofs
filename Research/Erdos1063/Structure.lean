module

public import Research.Erdos1063.Existence
public import Research.Erdos1063.StatementGate

@[expose] public section

/-!
# Erdős 1063: the structure of an admissible `n` (rickyc's argument, jbell31's search)

Let `n ≥ 2k` have exactly one failing index `e`: `(n - e) ∤ C(n, k)`, while `(n - i) ∣ C(n, k)`
for every other `i < k` (`Admissible n k e`; exactly FC's set). Every statement here holds for
every such `n`, not only for `n_k`.

* `unique_max`: for a prime `p ∣ k`, `n - e` is the unique factor of maximal `p`-adic valuation.
* `pow_dvd_sub`: `p^(a + v_p(C(k-1, e)) + ⌊log_p max(e, k-1-e)⌋) ∣ n - e` for `p^a ∥ k`.
* `eq_mod`, `D_dvd`: so `e = n mod k`, and `n ≡ e (mod D(k, e))`.
* `wheel`: for a prime `k/2 < p ≤ k`, a lone multiple of `p` in the window sits at index `e`.
* `lower_bound`: `n_k ≥ ∏_{p^a ∥ k} p^(a + ⌊log_p(k-1)⌋)`; it says more than `n_k ≥ 2k` only for
  composite `k ≠ 4` (`lower_bound_six`: `72 ≤ n₆ ≤ 75`).

Sources (erdosproblems.com/1063 forum). The identity behind `pow_dvd_sub`, `e = n mod k`,
`D(k, e) ∣ n - e` and the lower bound come from rickyc's argument (2026-06-26 and 2026-07-10,
with GPT-5.5 Thinking and GPT-5.6 Sol), made there for `n = n_k`. jbell31 (2026-07-28) stated
them for every solution, packaged the modulus as `D(k, e)` and added the wheel (a skip rule in
their search code) to make a search for `n_k` (k ≤ 75) exhaustive. `D_dvd` and `wheel` are the
two mathematical facts that search's coverage argument uses; its computation itself is not
replicated here.
-/

namespace Erdos1063.Structure

open Erdos1063 Erdos1063.Local Nat Finset

variable {p n k e : ℕ}

/-- No carry happens at a level `j ≤ v_p(k)` or at a level `j > M`, where `M` bounds the
valuations of the factors. Hence `v_p(C(n,k)) + a ≤ M` whenever `p^a ∣ k`. -/
theorem carries_add_le {M a : ℕ} (hp : p.Prime) (hk : 0 < k) (hkn : k ≤ n)
    (hM : ∀ i < k, (n - i).factorization p ≤ M) (ha : p ^ a ∣ k) :
    (n.choose k).factorization p + a ≤ M := by
  -- some factor is divisible by `p^a`, so `a ≤ M`
  have haM : a ≤ M := by
    have hpa : 0 < p ^ a := pow_pos hp.pos a
    have hlt : n % p ^ a < k := (Nat.mod_lt n hpa).trans_le (Nat.le_of_dvd hk ha)
    have hdvd : p ^ a ∣ n - n % p ^ a := Nat.dvd_sub_mod n
    have hne : n - n % p ^ a ≠ 0 := by omega
    exact ((hp.pow_dvd_iff_le_factorization hne).mp hdvd).trans (hM _ hlt)
  rw [factorization_choose hp hkn (Nat.lt_add_one (Nat.log p n))]
  have hsub : {j ∈ Ico 1 (Nat.log p n + 1) | p ^ j ≤ k % p ^ j + (n - k) % p ^ j} ⊆
      Ico (a + 1) (M + 1) := by
    intro j hj
    rw [mem_filter, mem_Ico] at hj
    obtain ⟨⟨hj1, -⟩, hc⟩ := hj
    rw [carry_iff (pow_pos hp.pos j) hkn] at hc
    rw [mem_Ico]
    constructor
    · by_contra hja
      push Not at hja
      have : k % p ^ j = 0 :=
        Nat.mod_eq_zero_of_dvd ((Nat.pow_dvd_pow p (by omega)).trans ha)
      rw [this] at hc
      exact Nat.not_lt_zero _ hc
    · by_contra hjM
      push Not at hjM
      -- `n % p^j < k` would make `p^j` divide the factor at index `n % p^j`
      have hk' : k % p ^ j ≤ k := Nat.mod_le k _
      have hlt : n % p ^ j < k := by omega
      have hdvd : p ^ j ∣ n - n % p ^ j := Nat.dvd_sub_mod n
      have hne : n - n % p ^ j ≠ 0 := by omega
      have := (hp.pow_dvd_iff_le_factorization hne).mp hdvd
      have := hM _ hlt
      omega
  have hc := card_le_card hsub
  rw [Nat.card_Ico] at hc
  omega

/-- The hypotheses "`n ≥ 2k` and `e` is the only failing index". -/
structure Admissible (n k e : ℕ) : Prop where
  two_mul_le : 2 * k ≤ n
  lt : e < k
  fails : ¬ (n - e) ∣ n.choose k
  divides : ∀ i < k, i ≠ e → (n - i) ∣ n.choose k

theorem admissible_of_mem {m : ℕ} (hm : m ∈ Existence.admissible k) :
    ∃ e, Admissible m k e := by
  obtain ⟨h2k, e, hek, hfail, hdiv⟩ := hm
  exact ⟨e, ⟨h2k, hek, hfail, hdiv⟩⟩

/-- **Unique maximum** (rickyc). For a prime `p ∣ k`, `n - e` is the only factor of maximal
`p`-adic valuation. -/
theorem unique_max (hA : Admissible n k e) (hp : p.Prime) (hpk : p ∣ k) {i : ℕ} (hik : i < k)
    (hie : i ≠ e) : (n - i).factorization p < (n - e).factorization p := by
  have hk : 0 < k := by have := hA.lt; omega
  have hkn : k ≤ n := by have := hA.two_mul_le; omega
  have hC : n.choose k ≠ 0 := Nat.pos_iff_ne_zero.mp (choose_pos hkn)
  -- the maximal valuation `M`, attained at some `j`
  obtain ⟨j, hj, hjmax⟩ := exists_max_image (range k) (fun i => (n - i).factorization p)
    ⟨0, mem_range.mpr hk⟩
  set M := (n - j).factorization p with hMdef
  have hM : ∀ i < k, (n - i).factorization p ≤ M := fun i hi => hjmax i (mem_range.mpr hi)
  have hS := carries_add_le hp hk hkn hM (pow_one p ▸ hpk)
  -- a factor of valuation `M` cannot divide `C(n,k)`, so it is the failing one
  have hfail_of : ∀ i < k, (n - i).factorization p = M → i = e := by
    intro i hi hiM
    by_contra hne
    have hdvd := hA.divides i hi hne
    have := (Nat.factorization_le_iff_dvd (by omega) hC).mpr hdvd p
    omega
  have hje : j = e := hfail_of j (mem_range.mp hj) rfl
  have hle := hM i hik
  have hneq : (n - i).factorization p ≠ M := fun h => hie (hfail_of i hik h)
  rw [← hje]
  omega

theorem two_le (hA : Admissible n k e) : 2 ≤ k := by
  by_contra h
  push Not at h
  have hk1 : k = 1 := by have := hA.lt; omega
  have he : e = 0 := by have := hA.lt; omega
  apply hA.fails
  rw [hk1, he, Nat.sub_zero, choose_one_right]

/-- Every other factor's distance to `e` has smaller `p`-adic valuation than `n - e`. -/
theorem dist_lt (hA : Admissible n k e) (hp : p.Prime) (hpk : p ∣ k) {i : ℕ} (hik : i < k)
    (hie : i ≠ e) : (Nat.dist e i).factorization p < (n - e).factorization p := by
  have hkn : k ≤ n := by have := hA.two_mul_le; omega
  have hek := hA.lt
  set M := (n - e).factorization p with hM
  by_contra hge
  push Not at hge
  have hd0 : Nat.dist e i ≠ 0 := (dist_pos_lt hek hik hie).1.ne'
  have h1 : p ^ M ∣ Nat.dist e i := (hp.pow_dvd_iff_le_factorization hd0).mpr hge
  have h2 : p ^ M ∣ n - e := Nat.ordProj_dvd _ _
  have h3 : p ^ M ∣ n - i := by
    rcases lt_or_gt_of_ne hie with h | h
    · have : Nat.dist e i = e - i := by simp [Nat.dist]; omega
      rw [this] at h1
      rw [show n - i = (n - e) + (e - i) by omega]
      exact dvd_add h2 h1
    · have : Nat.dist e i = i - e := by simp [Nat.dist]; omega
      rw [this] at h1
      rw [show n - i = (n - e) - (i - e) by omega]
      exact Nat.dvd_sub h2 h1
  have h4 := (hp.pow_dvd_iff_le_factorization (by omega : n - i ≠ 0)).mp h3
  have h5 := unique_max hA hp hpk hik hie
  omega

/-- **rickyc's divisibility.** For a prime `p ∣ k`,
`p^(v_p(k) + v_p(C(k-1, e)) + ⌊log_p max(e, k-1-e)⌋)` divides `n - e`. -/
theorem pow_dvd_sub (hA : Admissible n k e) (hp : p.Prime) (hpk : p ∣ k) :
    p ^ (k.factorization p + ((k - 1).choose e).factorization p +
      Nat.log p (max e (k - 1 - e))) ∣ n - e := by
  have hk2 := two_le hA
  have hek := hA.lt
  have hkn : k ≤ n := by have := hA.two_mul_le; omega
  have hN : n - e ≠ 0 := by omega
  have hC : n.choose k ≠ 0 := Nat.pos_iff_ne_zero.mp (choose_pos hkn)
  have hn : e + (n - e) = n := by omega
  have hdist : ∀ i < k, i ≠ e → (Nat.dist e i).factorization p < (n - e).factorization p :=
    fun i hik hie => dist_lt hA hp hpk hik hie
  have hstab := stabilization_of_dist hp hek (by omega : k ≤ e + (n - e)) hN hdist
  rw [hn, Nat.factorization_mul (by omega) (Nat.pos_iff_ne_zero.mp (choose_pos (by omega)))]
    at hstab
  simp only [Finsupp.coe_add, Pi.add_apply] at hstab
  -- `v_p(C(n,k)) ≥ u`, from the factor at distance `p^u` from `e`
  set r := max e (k - 1 - e) with hr
  set u := Nat.log p r with hu
  have hr0 : r ≠ 0 := by omega
  have hpu : p ^ u ≤ r := Nat.pow_log_le_self p hr0
  have hpu1 : 1 ≤ p ^ u := Nat.one_le_pow _ _ hp.pos
  obtain ⟨i, hik, hie, hdi⟩ : ∃ i < k, i ≠ e ∧ Nat.dist e i = p ^ u := by
    rcases le_total (k - 1 - e) e with h | h
    · have hre : r = e := by rw [hr]; exact max_eq_left h
      refine ⟨e - p ^ u, by omega, by omega, ?_⟩
      simp [Nat.dist]; omega
    · have hre : r = k - 1 - e := by rw [hr]; exact max_eq_right h
      refine ⟨e + p ^ u, by omega, by omega, ?_⟩
      simp [Nat.dist]
  have hSu : u ≤ (n.choose k).factorization p := by
    have h1 := (Nat.factorization_le_iff_dvd (by omega) hC).mpr (hA.divides i hik hie) p
    have h2 := factorization_shift_of_dist hp hek (by omega : k ≤ e + (n - e)) hN hdist hik hie
    rw [hn, hdi, hp.factorization_pow, Finsupp.single_eq_same] at h2
    omega
  exact (hp.pow_dvd_iff_le_factorization hN).mpr (by omega)

/-- The failing index is `n mod k` (rickyc): `k ∣ n - e`. -/
theorem dvd_sub_e (hA : Admissible n k e) : k ∣ n - e := by
  have hk2 := two_le hA
  have hkn : k ≤ n := by have := hA.two_mul_le; omega
  have hN : n - e ≠ 0 := by have := hA.lt; omega
  rw [← Nat.factorization_le_iff_dvd (by omega) hN]
  intro q
  by_cases hq : q.Prime ∧ q ∣ k
  · have h := (hq.1.pow_dvd_iff_le_factorization hN).mp (pow_dvd_sub hA hq.1 hq.2)
    omega
  · have : k.factorization q = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      tauto
    simp [this]

theorem eq_mod (hA : Admissible n k e) : e = n % k := by
  have hd := dvd_sub_e hA
  have hek := hA.lt
  have hkn : e ≤ n := by have := hA.two_mul_le; omega
  obtain ⟨q, hq⟩ := hd
  rw [show n = e + k * q by omega, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hek]

/-- `⌊log_p(k-1)⌋ ≤ v_p(C(k-1, e)) + ⌊log_p max(e, k-1-e)⌋`: if `max(e, k-1-e) < p^t ≤ k - 1`,
adding `e` and `k-1-e` in base `p` carries at digit `t`. -/
theorem log_le_add (hp : p.Prime) (hk : 2 ≤ k) (hek : e < k) :
    Nat.log p (k - 1) ≤ ((k - 1).choose e).factorization p + Nat.log p (max e (k - 1 - e)) := by
  set t := Nat.log p (k - 1) with ht
  set r := max e (k - 1 - e) with hr
  set u := Nat.log p r with hu
  by_cases htu : t ≤ u
  · omega
  push Not at htu
  have hr0 : r ≠ 0 := by omega
  have hrp : r < p ^ (u + 1) := Nat.lt_pow_succ_log_self hp.one_lt r
  have hpt : p ^ t ≤ k - 1 := Nat.pow_log_le_self p (by omega)
  have hrt : r < p ^ t := hrp.trans_le (Nat.pow_le_pow_right hp.pos (by omega))
  -- `t ≤ u + 1`, because `p^t ≤ k - 1 ≤ 2r < p^(u+2)`
  have htu1 : t ≤ u + 1 := by
    by_contra h
    push Not at h
    have h1 : p ^ (u + 2) ≤ p ^ t := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ (u + 2) = p * p ^ (u + 1) := by ring
    have h3 : 2 * p ^ (u + 1) ≤ p * p ^ (u + 1) := Nat.mul_le_mul_right _ hp.two_le
    have h4 : k - 1 ≤ 2 * r := by omega
    omega
  -- one carry, at digit `t`
  have hcarry : 1 ≤ ((k - 1).choose e).factorization p := by
    rw [factorization_choose hp (by omega : e ≤ k - 1) (Nat.lt_add_one t)]
    apply Finset.card_pos.mpr
    refine ⟨t, ?_⟩
    rw [mem_filter, mem_Ico]
    refine ⟨⟨by omega, Nat.lt_add_one t⟩, ?_⟩
    rw [Nat.mod_eq_of_lt (by omega : e < p ^ t), Nat.mod_eq_of_lt (by omega : k - 1 - e < p ^ t)]
    omega
  omega

/-- jbell31's modulus: `D(k, e) = ∏_{p^a ∥ k} p^(a + v_p(C(k-1, e)) + ⌊log_p max(e, k-1-e)⌋)`. -/
def D (k e : ℕ) : ℕ :=
  ∏ q ∈ k.primeFactors,
    q ^ (k.factorization q + ((k - 1).choose e).factorization q + Nat.log q (max e (k - 1 - e)))

/-- Every admissible `n` with failing index `e` satisfies `n ≡ e (mod D(k, e))`. -/
theorem D_dvd (hA : Admissible n k e) : D k e ∣ n - e := by
  unfold D
  apply Finset.prod_dvd_of_isRelPrime
  · intro q hq q' hq' hne
    have hq1 := (Nat.mem_primeFactors.mp hq).1
    have hq2 := (Nat.mem_primeFactors.mp hq').1
    exact Nat.coprime_iff_isRelPrime.mp
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hq1 hq2).mpr hne))
  · intro q hq
    obtain ⟨hq1, hq2, -⟩ := Nat.mem_primeFactors.mp hq
    exact pow_dvd_sub hA hq1 hq2

/-- **rickyc's lower bound**: `n ≥ ∏_{p^a ∥ k} p^(a + ⌊log_p(k-1)⌋)`. -/
theorem prod_le (hA : Admissible n k e) :
    ∏ q ∈ k.primeFactors, q ^ (k.factorization q + Nat.log q (k - 1)) ≤ n := by
  have hk2 := two_le hA
  have hek := hA.lt
  have hN : 0 < n - e := by have := hA.two_mul_le; omega
  calc ∏ q ∈ k.primeFactors, q ^ (k.factorization q + Nat.log q (k - 1))
      ≤ D k e := by
        unfold D
        refine Finset.prod_le_prod fun q hq => ?_
        have hq1 := (Nat.mem_primeFactors.mp hq).1
        refine Nat.pow_le_pow_right hq1.pos ?_
        have := log_le_add hq1 hk2 hek
        omega
    _ ≤ n - e := Nat.le_of_dvd hN (D_dvd hA)
    _ ≤ n := Nat.sub_le n e

/-- The same facts for `Erdos1063.n k` itself (the section variable `n` is not used here). -/
theorem n_eq_mod {k : ℕ} (hk : 2 ≤ k) :
    ∃ e, Admissible (Erdos1063.n k) k e ∧ e = Erdos1063.n k % k ∧
      D k e ∣ Erdos1063.n k - e := by
  have hmem : Erdos1063.n k ∈ Existence.admissible k :=
    Nat.sInf_mem ⟨_, Existence.bigM_mem hk⟩
  obtain ⟨e, hA⟩ := admissible_of_mem hmem
  exact ⟨e, hA, eq_mod hA, D_dvd hA⟩

/-- **rickyc's lower bound** for `n_k`: `n_k ≥ ∏_{p^a ∥ k} p^(a + ⌊log_p(k-1)⌋)`. -/
theorem lower_bound {k : ℕ} (hk : 2 ≤ k) :
    ∏ q ∈ k.primeFactors, q ^ (k.factorization q + Nat.log q (k - 1)) ≤ Erdos1063.n k := by
  obtain ⟨e, hA, -, -⟩ := n_eq_mod hk
  exact prod_le hA

/-- Statement gate: the bound is sharp enough to be tested. At `k = 4` it reads `8 ≤ n₄ = 9`, and
the deliberately false strengthening with exponent `a + ⌊log_p(k-1)⌋ + 1` fails there. -/
theorem not_lower_bound_succ :
    ¬ ∀ k, 2 ≤ k →
      ∏ q ∈ k.primeFactors, q ^ (k.factorization q + Nat.log q (k - 1) + 1) ≤ Erdos1063.n k := by
  intro h
  have h4 := h 4 (by norm_num)
  rw [Gate.n_four] at h4
  have hpf : (4 : ℕ).primeFactors = {2} := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  have hf : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.prime_two.factorization_pow, Finsupp.single_eq_same]
  have hl : Nat.log 2 (4 - 1) = 1 := by norm_num [Nat.log]
  rw [hpf, Finset.prod_singleton, hf, hl] at h4
  norm_num at h4

/-- `v_p(k!) = 1` for a prime `k/2 < p ≤ k`. -/
theorem factorization_factorial_eq_one (hp : p.Prime) (hpk : p ≤ k) (hk2p : k < 2 * p) :
    (k !).factorization p = 1 := by
  have hlog : Nat.log p k < 2 := by
    apply Nat.log_lt_of_lt_pow (by omega)
    calc k < 2 * p := hk2p
      _ ≤ p * p := Nat.mul_le_mul_right p hp.two_le
      _ = p ^ 2 := by ring
  rw [factorization_factorial hp hlog, show Ico 1 2 = {1} by rfl, sum_singleton, pow_one]
  exact le_antisymm (Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hp.pos).mpr (by omega)))
    ((Nat.le_div_iff_mul_le hp.pos).mpr (by omega))

/-- **jbell31's wheel** (the skip rule of their sweep). For a prime `k/2 < p ≤ k`: if the window
`n, n-1, …, n-k+1` holds only one multiple of `p`, namely when `n % p + p ≥ k`, then that
multiple, at index `n % p`, is the failing one. -/
theorem wheel (hA : Admissible n k e) (hp : p.Prime) (hpk : p ≤ k) (hk2p : k < 2 * p)
    (hone : k ≤ n % p + p) : n % p = e := by
  have hkn : k ≤ n := by have := hA.two_mul_le; omega
  set m := n % p with hm
  have hmp : m < p := Nat.mod_lt n hp.pos
  have hmk : m < k := hmp.trans_le hpk
  by_contra hme
  have hdvd := hA.divides m hmk hme
  have hC : n.choose k ≠ 0 := Nat.pos_iff_ne_zero.mp (choose_pos hkn)
  have hpm : p ∣ n - m := Nat.dvd_sub_mod n
  have hne : ∀ j ∈ range k, n - j ≠ 0 := fun j hj => by have := mem_range.mp hj; omega
  -- `p` divides no other factor of the window
  have hsum : (∏ j ∈ range k, (n - j)).factorization p = (n - m).factorization p := by
    rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single m]
    · intro j hj hjm
      have hj := mem_range.mp hj
      apply Nat.factorization_eq_zero_of_not_dvd
      intro hpj
      rcases lt_or_gt_of_ne hjm with h | h
      · have h1 : p ∣ m - j := by
          have := Nat.dvd_sub hpj hpm
          rwa [show n - j - (n - m) = m - j by omega] at this
        have := Nat.le_of_dvd (by omega) h1
        omega
      · have h1 : p ∣ j - m := by
          have := Nat.dvd_sub hpm hpj
          rwa [show n - m - (n - j) = j - m by omega] at this
        have := Nat.le_of_dvd (by omega) h1
        omega
    · intro hm'
      exact absurd (mem_range.mpr hmk) hm'
  have hdesc := descFactorial_eq_factorial_mul_choose n k
  rw [descFactorial_eq_prod_range] at hdesc
  rw [hdesc, Nat.factorization_mul (factorial_ne_zero k) hC] at hsum
  simp only [Finsupp.coe_add, Pi.add_apply] at hsum
  have h1 := factorization_factorial_eq_one hp hpk hk2p
  have h2 := (Nat.factorization_le_iff_dvd (by omega) hC).mpr hdvd p
  omega

/-! ### Statement gate at `k = 6`, where the lower bound says more than `n_k ≥ 2k`
(proposed by an independent review) -/

theorem prod_six : ∏ q ∈ (6 : ℕ).primeFactors,
    q ^ ((6 : ℕ).factorization q + Nat.log q (6 - 1)) = 72 := by
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.prime_two.primeFactors, Nat.prime_three.primeFactors]; rfl
  have h2 : (6 : ℕ).factorization 2 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have h3 : (6 : ℕ).factorization 3 = 1 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num)]
    simp [Nat.prime_two.factorization, Nat.prime_three.factorization]
  have l2 : Nat.log 2 (6 - 1) = 2 := by norm_num [Nat.log]
  have l3 : Nat.log 3 (6 - 1) = 1 := by norm_num [Nat.log]
  rw [hpf, Finset.prod_insert (by decide), Finset.prod_singleton, h2, h3, l2, l3]; norm_num

theorem choose_75_6 : Nat.choose 75 6 = 201359550 := by
  rw [Nat.choose_eq_descFactorial_div_factorial]; decide

/-- `n₆ ≤ 75`: `75` is admissible with failing index `3`. -/
theorem n_six_le : Erdos1063.n 6 ≤ 75 := by
  apply Nat.sInf_le
  refine ⟨by norm_num, 3, by norm_num, ?_, ?_⟩
  · rw [choose_75_6]; decide
  · rw [choose_75_6]; decide

/-- `72 ≤ n₆ ≤ 75`: at `k = 6` the lower bound is far above `2k = 12`, and within 4 of the truth. -/
theorem lower_bound_six : 72 ≤ Erdos1063.n 6 ∧ Erdos1063.n 6 ≤ 75 :=
  ⟨prod_six ▸ lower_bound (k := 6) (by norm_num), n_six_le⟩

end Erdos1063.Structure
