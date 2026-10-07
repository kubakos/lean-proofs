module

public import Research.Erdos1063.Main

@[expose] public section

/-!
# Erdős 1063: a subexponential bound, `nₖ ≤ exp(C·k·log log k / log k)`

The same construction as `Main`, with the same size estimates, but a sharper last step. `Main`
spends the box factor `B = ⌈k/e⌉` through `B³² ≤ 2e`, which caps the result at `2^(k/4)`.
Here the exponent grows with `k`: with `L = ⌊log₂ k⌋`, `m = ⌊log₂ L⌋ + 1` and
`c = ⌊L/(4m)⌋`, `B^c ≤ 2e`, so `B^|P| ≤ 2^(2k/c + 1)`, and `log₂ nₖ = O(k·m/L)`.

* `core_subexp`: for `L ≥ 64` and `2^L ≤ k < 2^(L+1)`, `n k ≤ 2^X` with `L·X ≤ 32·k·m`.
* `n_le_exp_of_ge`, `n_le_exp`: `nₖ ≤ exp(100·k·log log k / log k)` for every `k ≥ 2^64`.
  With `C = 100` this beats Cambie's `e^{(1+o(1))k}` only once `k ≳ 10^281`, and `Main`'s
  `2^(k/4)` only once `k ≳ 10^2130`: it is an asymptotic statement, not a usable estimate.
* `subexp_bound : SubexpBound`, the statement of P. White & Claude's claimed theorem
  (2026-07-25, unreviewed; <https://github.com/pw/erdos1063-upper-bound> at `a28481f5`), and
  of R. Cipollini's first bound. The construction is Cipollini's / GPT-5.6 Sol's; White &
  Claude's own argument is a different construction and is not checked here.
* `exp_littleO`: `nₖ = exp(o(k))`, their "in particular".
-/

namespace Erdos1063.Subexp

open Erdos1063 Erdos1063.Construction Erdos1063.Estimates Erdos1063.Box Nat Finset Filter

/-- "There is an absolute constant `C` such that, for all sufficiently large `k`,
`n_k ≤ exp(C · k·log log k / log k)`" (White & Claude, 2026-07-25). -/
def SubexpBound : Prop :=
  ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ Real.exp (C * k * Real.log (Real.log k) / Real.log k)

/-- `x^c ≤ 2^N` with `c ≥ 1` forces `x ≤ 2^(N/c + 1)`. -/
theorem le_of_pow_le {x c N : ℕ} (hc : 0 < c) (h : x ^ c ≤ 2 ^ N) : x ≤ 2 ^ (N / c + 1) := by
  by_contra hlt
  push Not at hlt
  have h1 : (2 ^ (N / c + 1)) ^ c < x ^ c := Nat.pow_lt_pow_left hlt hc.ne'
  have h2 : 2 ^ N ≤ (2 ^ (N / c + 1)) ^ c := by
    rw [← pow_mul]
    refine Nat.pow_le_pow_right (by norm_num) ?_
    have := Nat.lt_div_mul_add (a := N) hc
    rw [add_mul, one_mul]
    omega
  omega

/-- `8t + 8 ≤ 2^t` for `t ≥ 6`. -/
theorem eight_mul_add_le_two_pow {t : ℕ} (ht : 6 ≤ t) : 8 * t + 8 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    have : 8 ≤ 2 ^ t := (show 8 ≤ 2 ^ 3 by norm_num).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    omega

/-- `8·(⌊log₂ L⌋ + 1) ≤ L` for `L ≥ 64`. -/
theorem eight_log_le {L : ℕ} (hL : 64 ≤ L) : 8 * (Nat.log 2 L + 1) ≤ L := by
  have h6 : 6 ≤ Nat.log 2 L := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have := eight_mul_add_le_two_pow h6
  have := Nat.pow_log_le_self 2 (by omega : L ≠ 0)
  omega

/-- `L^4 ≤ 2^L` for `L ≥ 16`. -/
theorem pow_four_le_two_pow {L : ℕ} (hL : 16 ≤ L) : L ^ 4 ≤ 2 ^ L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ 2 L]
    have h : (L + 1) ^ 4 ≤ 2 * L ^ 4 := by
      have h1 : 4 * L ^ 3 + 6 * L ^ 2 + 4 * L + 1 ≤ L ^ 4 := by
        have : 16 * L ^ 3 ≤ L ^ 4 := by
          rw [show L ^ 4 = L * L ^ 3 by ring]; exact Nat.mul_le_mul_right _ hL
        have : 6 * L ^ 2 + 4 * L + 1 ≤ 12 * L ^ 3 := by nlinarith
        omega
      nlinarith
    omega

/-- The core bound. For `L ≥ 64` and `2^L ≤ k < 2^(L+1)`, some `X` has `n k ≤ 2^X` and
`L·X ≤ 32·k·(⌊log₂ L⌋ + 1)`. -/
theorem core_subexp {L k : ℕ} (hL : 64 ≤ L) (hk1 : 2 ^ L ≤ k) (hk2 : k < 2 ^ (L + 1)) :
    ∃ X, n k ≤ 2 ^ X ∧ L * X ≤ 32 * (k * (Nat.log 2 L + 1)) := by
  set s := L * L with hs
  set e := k / s with he
  set m := Nat.log 2 L + 1 with hm
  set c := L / (4 * m) with hc
  have hLk : L ^ 4 ≤ k := (pow_four_le_two_pow (by omega)).trans hk1
  have hs3 : 3 ≤ s := by rw [hs]; nlinarith
  have hs4 : s * s ≤ k := by rw [show s * s = L ^ 4 by rw [hs]; ring]; exact hLk
  have hes : e * s ≤ k := Nat.div_mul_le_self k s
  have hes2 : k < e * s + s := by
    have := Nat.lt_div_mul_add (a := k) (by omega : 0 < s); rw [← he] at this; exact this
  have h2s : 2 * s ≤ k := (Nat.mul_le_mul_right s (by omega)).trans hs4
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h0 | h0
    · rw [h0, zero_mul, zero_add] at hes2; omega
    · exact h0
  have hses : s ≤ e * s := Nat.le_mul_of_pos_left s he1
  have hk2es : k ≤ 2 * (e * s) := by omega
  have he3 : e * 3 ≤ e * s := Nat.mul_le_mul_left e hs3
  have hek : e < k := by omega
  have h2ek : 2 * e < k := by omega
  have hke : k ≤ 4 * e ^ 2 := by
    have h1 : k * k ≤ (2 * (e * s)) * (2 * (e * s)) := Nat.mul_le_mul hk2es hk2es
    have h2 : (2 * (e * s)) * (2 * (e * s)) = 4 * e ^ 2 * (s * s) := by ring
    have h3 : 4 * e ^ 2 * (s * s) ≤ 4 * e ^ 2 * k := Nat.mul_le_mul_left _ hs4
    exact Nat.le_of_mul_le_mul_right (by rw [← h2] at h3; omega) (by omega : 0 < k)
  have hn := n_le_construction (k := k) (e := e) (by omega) he1 hek hke
  have hB : ceilDiv k e ≤ 2 * s := by
    unfold ceilDiv
    refine Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr ?_)
    rw [show (2 * s).succ * e = 2 * (e * s) + e by rw [Nat.succ_mul]; ring]
    omega
  -- the exponent `c`
  have h8m : 8 * m ≤ L := eight_log_le hL
  have hm1 : 7 ≤ m := by
    have : 6 ≤ Nat.log 2 L := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
    omega
  have hLm : L < 2 ^ m := Nat.lt_pow_succ_log_self (by norm_num) L
  have hc1 : 1 ≤ c := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hcL : 4 * m * c ≤ L := by rw [mul_comm]; exact Nat.div_mul_le_self L (4 * m)
  have hLc : L ≤ 8 * m * c := by
    have := Nat.lt_div_mul_add (a := L) (by omega : 0 < 4 * m)
    rw [← hc] at this
    nlinarith
  -- `B^c ≤ 2e`
  have hs2m : s < 2 ^ (2 * m) := by
    rw [hs, two_mul, pow_add]; exact Nat.mul_lt_mul'' hLm hLm
  have hB2 : ceilDiv k e ≤ 2 ^ (2 * m + 1) := by
    rw [pow_succ]; omega
  have hexp : (2 * m + 1) * c + 2 * m ≤ L := by
    have : 4 * c ≤ L := by nlinarith
    nlinarith
  have hBc : ceilDiv k e ^ c ≤ 2 * e := by
    have h1 : ceilDiv k e ^ c ≤ 2 ^ ((2 * m + 1) * c) := by
      rw [pow_mul]; exact Nat.pow_le_pow_left hB2 c
    have h2 : 2 ^ ((2 * m + 1) * c) * 2 ^ (2 * m) < 2 * e * 2 ^ (2 * m) := by
      calc 2 ^ ((2 * m + 1) * c) * 2 ^ (2 * m) = 2 ^ ((2 * m + 1) * c + 2 * m) := by
            rw [← pow_add]
        _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hexp
        _ ≤ k := hk1
        _ ≤ 2 * (e * s) := hk2es
        _ < 2 * e * 2 ^ (2 * m) := by
            rw [← mul_assoc]; exact Nat.mul_lt_mul_of_pos_left hs2m (by omega)
    exact h1.trans (Nat.lt_of_mul_lt_mul_right h2).le
  -- `B^|P| ≤ 2^(2k/c + 1)`
  have hBP : ceilDiv k e ^ #(Pset k e) ≤ 2 ^ (2 * k / c + 1) := by
    apply le_of_pow_le (by omega)
    calc (ceilDiv k e ^ #(Pset k e)) ^ c = (ceilDiv k e ^ c) ^ #(Pset k e) := by ring
      _ ≤ (2 * e) ^ #(Pset k e) := Nat.pow_le_pow_left hBc _
      _ ≤ 4 ^ k := two_e_pow_card_le
      _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have hkpow : ∀ j, k ^ j ≤ 2 ^ ((L + 1) * j) := fun j => by
    rw [pow_mul]; exact Nat.pow_le_pow_left hk2.le j
  have hM : Mmain k e ≤ 2 ^ ((L + 1) * (6 * e + 4)) := (Mmain_le hek h2ek.le).trans (hkpow _)
  have hQ : Qbox k e ≤ 2 ^ (2 * k / c + 1) * 2 ^ ((L + 1) * e) :=
    (Qbox_le he1 hek h2ek).trans (Nat.mul_le_mul hBP (hkpow e))
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (L + 1) * (6 * e + 4) + (2 * k / c + 1) + (L + 1) * e := ⟨_, rfl⟩
  have hYL : L + 1 ≤ Y := by
    rw [hY]
    exact (Nat.le_mul_of_pos_right _ (by omega : 0 < 6 * e + 4)).trans (le_add_right (le_add_right le_rfl))
  have he2 : e ≤ 2 ^ Y := hek.le.trans (hk2.le.trans (Nat.pow_le_pow_right (by norm_num) hYL))
  refine ⟨Y + 1, ?_, ?_⟩
  · calc n k ≤ e + Mmain k e * Qbox k e := hn
      _ ≤ 2 ^ Y + 2 ^ ((L + 1) * (6 * e + 4)) * (2 ^ (2 * k / c + 1) * 2 ^ ((L + 1) * e)) :=
          Nat.add_le_add he2 (Nat.mul_le_mul hM hQ)
      _ = 2 ^ Y + 2 ^ Y := by rw [hY]; ring
      _ = 2 ^ (Y + 1) := by rw [pow_succ]; ring
  · -- `L·(Y+1) ≤ 32·k·m`, with `k·m` kept as one atom for `omega`
    have hLe : L * ((L + 1) * e) ≤ 2 * k := by
      have h1 : L * ((L + 1) * e) ≤ 2 * (e * (L * L)) := by
        have : L + 1 ≤ 2 * L := by omega
        calc L * ((L + 1) * e) = (L + 1) * (L * e) := by ring
          _ ≤ (2 * L) * (L * e) := Nat.mul_le_mul_right _ this
          _ = 2 * (e * (L * L)) := by ring
      rw [← hs] at h1
      omega
    have hLc2 : L * (2 * k / c) ≤ 16 * (k * m) := by
      have h1 : 2 * k / c * c ≤ 2 * k := Nat.div_mul_le_self _ _
      calc L * (2 * k / c) ≤ 8 * m * c * (2 * k / c) := Nat.mul_le_mul_right _ hLc
        _ = 8 * m * (2 * k / c * c) := by ring
        _ ≤ 8 * m * (2 * k) := Nat.mul_le_mul_left _ h1
        _ = 16 * (k * m) := by ring
    have hL4 : L * (4 * (L + 1)) ≤ 4 * k := by
      have h1 : L * (4 * (L + 1)) ≤ 8 * (L * L) := by
        calc L * (4 * (L + 1)) = 4 * (L * L) + 4 * L := by ring
          _ ≤ 4 * (L * L) + 4 * (L * L) := by
              have : L ≤ L * L := Nat.le_mul_of_pos_left L (by omega)
              omega
          _ = 8 * (L * L) := by ring
      rw [← hs] at h1
      omega
    have hL2 : L * 2 ≤ k := by
      have : L * 2 ≤ L * L := Nat.mul_le_mul_left _ (by omega)
      rw [← hs] at this
      omega
    have hkm : 2 * k ≤ k * m := by
      have := Nat.mul_le_mul_left k (show 2 ≤ m by omega)
      rw [mul_comm k 2] at this
      exact this
    calc L * (Y + 1)
        = 7 * (L * ((L + 1) * e)) + L * (4 * (L + 1)) + L * (2 * k / c) + L * 2 := by
          rw [hY]; ring
      _ ≤ 32 * (k * m) := by omega

/-- `nₖ ≤ exp(100·k·log log k / log k)` for every `k ≥ 2^64`. -/
theorem n_le_exp_of_ge {k : ℕ} (hk : 2 ^ 64 ≤ k) :
    (n k : ℝ) ≤ Real.exp (100 * k * Real.log (Real.log k) / Real.log k) := by
  have hk0 : k ≠ 0 := by have := Nat.one_le_two_pow (n := 64); omega
  set L := Nat.log 2 k with hLdef
  have hL : 64 ≤ L := Nat.le_log_of_pow_le (by norm_num) hk
  have hk1 : 2 ^ L ≤ k := Nat.pow_log_le_self 2 hk0
  have hk2 : k < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) k
  obtain ⟨X, hnX, hLX⟩ := core_subexp hL hk1 hk2
  set m := Nat.log 2 L + 1 with hm
  have hmL : 2 ^ (m - 1) ≤ L := by
    rw [hm, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 2 (by omega)
  set a := Real.log 2 with ha
  have ha1 : 0.6931471803 < a := Real.log_two_gt_d9
  have ha2 : a < 0.6931471808 := Real.log_two_lt_d9
  have hLr : (64 : ℝ) ≤ L := by exact_mod_cast hL
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
  set lk := Real.log k with hlk
  have hlk1 : (L : ℝ) * a ≤ lk := by
    have : ((2 : ℝ) ^ L) ≤ k := by exact_mod_cast hk1
    calc (L : ℝ) * a = Real.log ((2 : ℝ) ^ L) := by rw [Real.log_pow]
      _ ≤ lk := Real.log_le_log (by positivity) this
  have hlk2 : lk ≤ 2 * L * a := by
    have : (k : ℝ) ≤ (2 : ℝ) ^ (L + 1) := by exact_mod_cast hk2.le
    have h := Real.log_le_log hkpos this
    rw [Real.log_pow] at h
    push_cast at h
    nlinarith
  have hlkpos : 0 < lk := by nlinarith
  set ℓ := Real.log L with hℓ
  have hℓ4 : 4 ≤ ℓ := by
    have h1 : Real.log 64 ≤ ℓ := Real.log_le_log (by norm_num) hLr
    have h64 : Real.log 64 = 6 * a := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow, ← ha]; norm_num
    linarith
  have hma : (m : ℝ) * a ≤ ℓ + a := by
    have h1 : ((2 : ℝ) ^ (m - 1)) ≤ L := by exact_mod_cast hmL
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have h3 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ m)]; simp
    rw [h3] at h2
    linarith
  have hloga : -1 < Real.log a := by
    rw [Real.lt_log_iff_exp_lt (by linarith)]
    have := Real.exp_neg_one_lt_d9
    linarith
  have hloglk : ℓ - 1 ≤ Real.log lk := by
    have h1 : Real.log ((L : ℝ) * a) ≤ Real.log lk := Real.log_le_log (by positivity) hlk1
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    linarith
  have hLXr : (L : ℝ) * X ≤ 32 * (k * m) := by exact_mod_cast hLX
  have hcore : 64 * a * (ℓ + a) ≤ 100 * (ℓ - 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha2.le) (by linarith : (0 : ℝ) ≤ ℓ)]
  have hexp : (X : ℝ) * a ≤ 100 * k * Real.log lk / lk := by
    rw [le_div_iff₀ hlkpos]
    have hXa : (0 : ℝ) ≤ X * a := by positivity
    calc (X : ℝ) * a * lk ≤ X * a * (2 * L * a) := mul_le_mul_of_nonneg_left hlk2 hXa
      _ = 2 * a ^ 2 * (L * X) := by ring
      _ ≤ 2 * a ^ 2 * (32 * (k * m)) := mul_le_mul_of_nonneg_left hLXr (by positivity)
      _ = 64 * a * k * (m * a) := by ring
      _ ≤ 64 * a * k * (ℓ + a) := mul_le_mul_of_nonneg_left hma (by positivity)
      _ = k * (64 * a * (ℓ + a)) := by ring
      _ ≤ k * (100 * (ℓ - 1)) := mul_le_mul_of_nonneg_left hcore hkpos.le
      _ ≤ k * (100 * Real.log lk) := by gcongr
      _ = 100 * k * Real.log lk := by ring
  calc (n k : ℝ) ≤ (2 : ℝ) ^ X := by exact_mod_cast hnX
    _ = Real.exp (X * a) := by rw [Real.exp_nat_mul, ha, Real.exp_log (by norm_num)]
    _ ≤ _ := Real.exp_le_exp.mpr hexp

/-- Eventually `nₖ ≤ exp(100·k·log log k / log k)`. -/
theorem n_le_exp : ∀ᶠ k : ℕ in atTop,
    (n k : ℝ) ≤ Real.exp (100 * k * Real.log (Real.log k) / Real.log k) :=
  eventually_atTop.mpr ⟨2 ^ 64, fun _ hk => n_le_exp_of_ge hk⟩

/-- **The statement White & Claude claim, Lean-checked**: `nₖ ≤ exp(C·k·log log k / log k)`
for all large `k`, with `C = 100`. The proof uses Cipollini's / GPT-5.6 Sol's construction;
White & Claude's own argument (a different construction) is not what is checked here. -/
theorem subexp_bound : SubexpBound := ⟨100, n_le_exp⟩

/-- Statement gate (proposed by an independent review): White & Claude's own "in
particular", `nₖ = exp(o(k))`. This puts `SubexpBound` strictly below Cambie's
`e^{(1+o(1))k}`, so a misformalization weaker than Cambie's bound could not pass. -/
theorem exp_littleO_of_subexp (h : SubexpBound) :
    ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ Real.exp (ε * k) := by
  obtain ⟨C, hC⟩ := h
  intro ε hε
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hr : Tendsto (fun k : ℕ => Real.log (Real.log k) / Real.log k) atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hlog
  have hr2 : ∀ᶠ k : ℕ in atTop, |C| * (Real.log (Real.log k) / Real.log k) ≤ ε := by
    have := hr.const_mul |C|
    rw [mul_zero] at this
    exact this.eventually (ge_mem_nhds hε)
  have hpos : ∀ᶠ k : ℕ in atTop, 0 ≤ Real.log (Real.log k) / Real.log k := by
    filter_upwards [hlog.eventually_ge_atTop 1] with k hk
    exact div_nonneg (Real.log_nonneg hk) (by linarith)
  filter_upwards [hC, hr2, hpos] with k hk h2 h3
  refine hk.trans (Real.exp_le_exp.mpr ?_)
  have hk0 : (0 : ℝ) ≤ k := by positivity
  calc C * k * Real.log (Real.log k) / Real.log k
      = (C * (Real.log (Real.log k) / Real.log k)) * k := by ring
    _ ≤ (|C| * (Real.log (Real.log k) / Real.log k)) * k := by
        gcongr; exact le_abs_self C
    _ ≤ ε * k := by gcongr

/-- `nₖ = exp(o(k))`, unconditionally. -/
theorem exp_littleO : ∀ ε > 0, ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ Real.exp (ε * k) :=
  exp_littleO_of_subexp subexp_bound

/-- Statement gate: the deliberately false variant without the factor `k` (which would make
`nₖ` bounded) is refuted, so the form of the bound matters. -/
theorem not_subexp_without_k :
    ¬ ∃ C : ℝ, ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ Real.exp (C * Real.log (Real.log k) / Real.log k) := by
  rintro ⟨C, hC⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp hC
  set K' := max K (max 3 (⌈Real.exp |C|⌉₊ + 1)) with hK'
  have hk3 : 3 ≤ K' := by omega
  have hbig : Real.exp |C| < K' := by
    have h1 : Real.exp |C| ≤ ⌈Real.exp |C|⌉₊ := Nat.le_ceil _
    have h2 : (⌈Real.exp |C|⌉₊ : ℝ) + 1 ≤ K' := by exact_mod_cast (by omega : ⌈Real.exp |C|⌉₊ + 1 ≤ K')
    linarith
  have hn := hK K' (by omega)
  have hlk : 1 < Real.log K' := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : (3 : ℝ) ≤ K' := by exact_mod_cast hk3
    linarith
  have hll0 : 0 ≤ Real.log (Real.log K') := Real.log_nonneg hlk.le
  have hll1 : Real.log (Real.log K') ≤ Real.log K' :=
    (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have hq : C * Real.log (Real.log K') / Real.log K' ≤ |C| := by
    rw [div_le_iff₀ (by linarith)]
    calc C * Real.log (Real.log K') ≤ |C| * Real.log (Real.log K') :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hll0
      _ ≤ |C| * Real.log K' := mul_le_mul_of_nonneg_left hll1 (abs_nonneg C)
  have h2k : (2 * K' : ℝ) ≤ n K' := by
    exact_mod_cast Existence.two_mul_le_n (by omega : 2 ≤ K')
  have : (n K' : ℝ) ≤ Real.exp |C| := hn.trans (Real.exp_le_exp.mpr hq)
  have : (0 : ℝ) ≤ K' := by positivity
  linarith

end Erdos1063.Subexp
