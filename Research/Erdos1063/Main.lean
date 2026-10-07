module

public import Research.Erdos1063.Estimates
public import Research.Erdos1063.Asymptotic

@[expose] public section

/-!
# Erdős 1063, FC `better_upper`: the main theorem

With `L = ⌊log₂ k⌋` and `e = k / L²`, the construction gives, for all large `k`,
`n k ≤ e + M·Q ≤ 2^(k/4)` (`n_le_two_pow`). Together with `Asymptotic.isLittleO_of_pow_bound`
this gives `nₖ = o(k · lcm(1..k-1))` (`isLittleO_cambie`). The headline result is
`better_upper_explicit`: the FC statement with the explicit answer `2^(k/4)`. (`better_upper`,
with the degenerate witness `n` itself, is formally valid but is not an answer.)

Credit: the construction is the claimed proof's (R. Cipollini / GPT-5.6 Sol, 2026, unreviewed;
<https://www.overleaf.com/read/hrpsqsnqktky>). The estimates here are cruder and use only the
primorial bound, so the result is the weaker FC target, not the claimed constant.
-/

namespace Erdos1063.Main

open Erdos1063 Erdos1063.Gate Erdos1063.Construction Erdos1063.Estimates Erdos1063.Asymptotic
  Erdos1063.Box Nat Finset Filter Asymptotics

/-- Eventually `L^70 ≤ 2^L`. -/
theorem eventually_pow_le_two_pow : ∀ᶠ L : ℕ in atTop, L ^ 70 ≤ 2 ^ L := by
  have h := (isLittleO_pow_const_const_pow_of_one_lt (R := ℝ) 70 (by norm_num : (1:ℝ) < 2)).bound
    one_pos
  filter_upwards [h] with L hL
  simp only [norm_pow, Real.norm_natCast, one_mul, Real.norm_ofNat] at hL
  exact_mod_cast hL

/-- `x^32 ≤ 2^(2k)` forces `x ≤ 2^(k/16 + 1)`. -/
theorem le_of_pow32_le {x k : ℕ} (h : x ^ 32 ≤ 2 ^ (2 * k)) : x ≤ 2 ^ (k / 16 + 1) := by
  by_contra hlt
  push Not at hlt
  have h1 : (2 ^ (k / 16 + 1)) ^ 32 < x ^ 32 := Nat.pow_lt_pow_left hlt (by norm_num)
  have h2 : 2 ^ (2 * k) ≤ (2 ^ (k / 16 + 1)) ^ 32 := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The core bound, for `L ≥ 6561` with `L^70 ≤ 2^L` and `2^L ≤ k < 2^(L+1)`. -/
theorem core_bound {L k : ℕ} (hL : 6561 ≤ L) (hpoly : L ^ 70 ≤ 2 ^ L) (hk1 : 2 ^ L ≤ k)
    (hk2 : k < 2 ^ (L + 1)) : n k ≤ 2 ^ (k / 4) := by
  set s := L * L with hs
  set e := k / s with he
  have hLk : L ^ 70 ≤ k := hpoly.trans hk1
  have hs3 : 3 ≤ s := by rw [hs]; nlinarith
  have hs4 : s * s ≤ k := by
    calc s * s = L ^ 4 := by rw [hs]; ring
      _ ≤ L ^ 70 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ ≤ k := hLk
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
  have hB32 : ceilDiv k e ^ 32 ≤ 2 * e := by
    have h1 : (2 * s) ^ 32 * s ≤ k := by
      calc (2 * s) ^ 32 * s = 2 ^ 32 * L ^ 66 := by rw [hs]; ring
        _ ≤ L ^ 4 * L ^ 66 := Nat.mul_le_mul_right _ (by
            calc 2 ^ 32 = 256 ^ 4 := by norm_num
              _ ≤ L ^ 4 := Nat.pow_le_pow_left (by omega) 4)
        _ = L ^ 70 := by ring
        _ ≤ k := hLk
    have h2 : (2 * s) ^ 32 * s ≤ (2 * e) * s := by
      rw [show (2 * e) * s = 2 * (e * s) by ring]; omega
    exact (Nat.pow_le_pow_left hB 32).trans (Nat.le_of_mul_le_mul_right h2 (by omega))
  have hBP : ceilDiv k e ^ #(Pset k e) ≤ 2 ^ (k / 16 + 1) := by
    apply le_of_pow32_le
    calc (ceilDiv k e ^ #(Pset k e)) ^ 32 = (ceilDiv k e ^ 32) ^ #(Pset k e) := by ring
      _ ≤ (2 * e) ^ #(Pset k e) := Nat.pow_le_pow_left hB32 _
      _ ≤ 4 ^ k := two_e_pow_card_le
      _ = 2 ^ (2 * k) := by rw [pow_mul]; norm_num
  have hkpow : ∀ m, k ^ m ≤ 2 ^ ((L + 1) * m) := fun m => by
    rw [pow_mul]; exact Nat.pow_le_pow_left hk2.le m
  have h16 : 16 * (L + 1) ≤ s := by rw [hs]; nlinarith
  have h192 : 192 * (L + 1) ≤ s := by rw [hs]; nlinarith
  have hLe : 16 * ((L + 1) * e) ≤ k := by
    have : (16 * (L + 1)) * e ≤ s * e := Nat.mul_le_mul_right e h16
    rw [show 16 * ((L + 1) * e) = (16 * (L + 1)) * e by ring]
    rw [show s * e = e * s by ring] at this
    omega
  have hLM : 16 * ((L + 1) * (6 * e + 4)) ≤ k := by
    have h1 : (192 * (L + 1)) * e ≤ s * e := Nat.mul_le_mul_right e h192
    have h2 : 128 * (L + 1) ≤ k := by
      have : 128 * (L + 1) ≤ s := by rw [hs]; nlinarith
      omega
    rw [show s * e = e * s by ring] at h1
    have h3 : 16 * ((L + 1) * (6 * e + 4)) = 96 * ((L + 1) * e) + 64 * (L + 1) := by ring
    have h4 : (192 * (L + 1)) * e = 192 * ((L + 1) * e) := by ring
    omega
  have hke' : k ^ e ≤ 2 ^ (k / 16) :=
    (hkpow e).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hM : Mmain k e ≤ 2 ^ (k / 16) :=
    (Mmain_le hek h2ek.le).trans ((hkpow _).trans (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have hQ : Qbox k e ≤ 2 ^ (k / 16 + 1) * 2 ^ (k / 16) :=
    (Qbox_le he1 hek h2ek).trans (Nat.mul_le_mul hBP hke')
  have hLk16 : L + 1 ≤ k / 16 := by
    have : 16 * (L + 1) ≤ k := h16.trans (by omega)
    omega
  have he16 : e ≤ 2 ^ (k / 16) :=
    hek.le.trans (hk2.le.trans (Nat.pow_le_pow_right (by norm_num) hLk16))
  set a := k / 16 with ha_def
  have ha : 2 ≤ a := by omega
  calc n k ≤ e + Mmain k e * Qbox k e := hn
    _ ≤ 2 ^ a + 2 ^ a * (2 ^ (a + 1) * 2 ^ a) := Nat.add_le_add he16 (Nat.mul_le_mul hM hQ)
    _ = 2 ^ a + 2 ^ (3 * a + 1) := by
        congr 1; rw [← pow_add, ← pow_add]; congr 1; omega
    _ ≤ 2 ^ (3 * a + 1) + 2 ^ (3 * a + 1) :=
        Nat.add_le_add_right (Nat.pow_le_pow_right (by norm_num) (by omega)) _
    _ = 2 ^ (3 * a + 2) := by rw [pow_succ 2 (3 * a + 1)]; ring
    _ ≤ 2 ^ (k / 4) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem n_le_two_pow : ∀ᶠ k in atTop, n k ≤ 2 ^ (k / 4) := by
  obtain ⟨L0, hL0⟩ := eventually_atTop.mp eventually_pow_le_two_pow
  refine eventually_atTop.mpr ⟨2 ^ (max L0 6561), fun k hk => ?_⟩
  have hk0 : k ≠ 0 := by have := Nat.one_le_two_pow (n := max L0 6561); omega
  set L := Nat.log 2 k
  have hLge : max L0 6561 ≤ L := Nat.le_log_of_pow_le (by norm_num) hk
  exact core_bound (by omega) (hL0 L (by omega)) (Nat.pow_log_le_self 2 hk0)
    (Nat.lt_pow_succ_log_self (by norm_num) k)

/-- `nₖ = o(k · lcm(1..k-1))`. -/
theorem isLittleO_cambie : (fun k => (n k : ℝ)) =o[atTop] cambie :=
  isLittleO_of_pow_bound n_le_two_pow

/-- The transcribed FC statement with the **degenerate** witness `upper_bound := n`. Formally
valid, but it answers nothing (`Gate.statement_iff`). Cite `better_upper_explicit` as the
answer, never this. -/
theorem better_upper : Erdos1063.Statement (fun k => (n k : ℝ)) :=
  ⟨isBigO_refl _ _, isLittleO_cambie⟩

/-- The explicit bound `2^(k/4)` is itself `o(k · lcm(1..k-1))`. -/
theorem two_pow_quarter_isLittleO :
    (fun k : ℕ => (2 : ℝ) ^ (k / 4)) =o[atTop] cambie := by
  refine IsLittleO.of_bound fun c hc => ?_
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (1 / c) (by norm_num : (1 : ℝ) < 2)
  filter_upwards [eventually_ge_atTop (4 * K + 8)] with k hkK
  have hcam := cambie_ge (k := k) (by omega)
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg ((by positivity : (0:ℝ) ≤ 2 ^ (k - 1)).trans hcam)]
  have h2 : (2 : ℝ) ^ (k / 4) * 2 ^ K ≤ 2 ^ (k - 1) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : 1 ≤ c * 2 ^ K := by
    have := hK.le
    rw [div_le_iff₀ hc] at this
    linarith [mul_comm c ((2:ℝ) ^ K)]
  calc (2 : ℝ) ^ (k / 4) ≤ 2 ^ (k / 4) * (c * 2 ^ K) := le_mul_of_one_le_right (by positivity) h3
    _ = c * (2 ^ (k / 4) * 2 ^ K) := by ring
    _ ≤ c * 2 ^ (k - 1) := by gcongr
    _ ≤ c * cambie k := by gcongr

/-- **FC `erdos_1063.better_upper` with an explicit answer**: `nₖ = O(2^(k/4))`, and
`2^(k/4) = o(k · lcm(1..k-1))`. This improves Cambie's `nₖ ≤ k · lcm(1..k-1)` by a factor
that tends to infinity. -/
theorem better_upper_explicit : Erdos1063.Statement (fun k => (2 : ℝ) ^ (k / 4)) := by
  refine ⟨IsBigO.of_bound 1 ?_, two_pow_quarter_isLittleO⟩
  filter_upwards [n_le_two_pow] with k hk
  rw [Real.norm_natCast, Real.norm_of_nonneg (by positivity), one_mul]
  exact_mod_cast hk

/-- Sanity check: the comparator at `k = 5` is `5 · lcm(1..4) = 60`. -/
theorem cambie_five : cambie 5 = 60 := by
  have h : (Finset.Icc 1 (5 - 1)).lcm id = 12 := by decide
  unfold cambie; rw [h]; norm_num

/-- The "better" requirement bites: Cambie's own bound is not an answer. (Contributed by an
independent review, 2026-10-06.) -/
theorem not_statement_cambie : ¬ Erdos1063.Statement cambie := by
  rintro ⟨-, h⟩
  obtain ⟨K, hK⟩ := eventually_atTop.mp (h.bound (c := 1 / 2) (by norm_num))
  have hk := hK (K + 1) (by omega)
  have hpos := (pow_pos (by norm_num : (0:ℝ) < 2) (K + 1 - 1)).trans_le
    (cambie_ge (k := K + 1) (by omega))
  change ‖cambie (K + 1)‖ ≤ 1 / 2 * ‖cambie (K + 1)‖ at hk
  rw [Real.norm_of_nonneg hpos.le] at hk
  linarith

end Erdos1063.Main
