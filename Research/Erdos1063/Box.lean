module

public import Mathlib

@[expose] public section

/-!
# Erdős 1063: the two-sided box principle (plan step 6)

For a finite set `P` of positive moduli, block sizes `h p ≥ 1`, and any `M`, there is
`1 ≤ t ≤ ∏_{p ∈ P} ⌈p / h p⌉` such that, for each `p ∈ P`, `t·M mod p` lies within `h p` of
`0`: either `t·M % p < h p` or `p - t·M % p < h p`. Pigeonhole on the block indices
`⌊(j·M % p) / h p⌋` for `j = 0, …, Q`.
-/

namespace Erdos1063.Box

open Finset

/-- `⌈p / h⌉` in `ℕ`. -/
def ceilDiv (p h : ℕ) : ℕ := (p + h - 1) / h

theorem lt_mul_ceilDiv {p h : ℕ} (hh : 0 < h) : p ≤ ceilDiv p h * h := by
  unfold ceilDiv
  have h1 := Nat.div_add_mod (p + h - 1) h
  have h2 := Nat.mod_lt (p + h - 1) hh
  rw [mul_comm]
  omega

/-- Two residues `a b < p` in the same block of size `h` differ by less than `h`. -/
theorem sub_lt_of_div_eq {a b h : ℕ} (hh : 0 < h) (hab : a / h = b / h) : a - b < h := by
  have ha := Nat.div_add_mod a h
  have hb := Nat.div_add_mod b h
  have := Nat.mod_lt a hh
  have := Nat.mod_lt b hh
  rw [hab] at ha
  omega

/-- From `(a + c) % p = b` with `a, b, c < p`, the residue `c` is within `h` of `0` when
`|a - b| < h`. -/
theorem near_zero {p a b c h : ℕ} (ha : a < p) (hc : c < p)
    (habc : (a + c) % p = b) (h1 : a - b < h) (h2 : b - a < h) :
    c < h ∨ p - c < h := by
  rcases Nat.lt_or_ge (a + c) p with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at habc
    left; omega
  · have : (a + c) % p = a + c - p := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [this] at habc
    right; omega

theorem exists_small_multiple (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (h : ℕ → ℕ)
    (hh : ∀ p ∈ P, 0 < h p) (M : ℕ) :
    ∃ t, 1 ≤ t ∧ t ≤ ∏ p ∈ P, ceilDiv p (h p) ∧
      ∀ p ∈ P, t * M % p < h p ∨ p - t * M % p < h p := by
  set Q := ∏ p ∈ P, ceilDiv p (h p)
  -- block index map into the finite product of ranges
  let f : ℕ → (a : ℕ) → a ∈ P → ℕ := fun j p _ => (j * M % p) / h p
  have hmaps : ∀ j ∈ range (Q + 1), f j ∈ P.pi fun p => range (ceilDiv p (h p)) := by
    intro j _
    rw [mem_pi]
    intro p hpP
    rw [mem_range]
    apply Nat.div_lt_of_lt_mul
    calc j * M % p < p := Nat.mod_lt _ (hP p hpP)
      _ ≤ ceilDiv p (h p) * h p := lt_mul_ceilDiv (hh p hpP)
      _ = h p * ceilDiv p (h p) := mul_comm _ _
  have hcard : (P.pi fun p => range (ceilDiv p (h p))).card < (range (Q + 1)).card := by
    rw [card_pi, card_range]
    simp only [card_range]
    omega
  obtain ⟨x, hx, y, hy, hxy, hfxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  -- WLOG x < y; set t = y - x
  have key : ∀ x y, x < y → y ≤ Q → f x = f y →
      ∃ t, 1 ≤ t ∧ t ≤ Q ∧ ∀ p ∈ P, t * M % p < h p ∨ p - t * M % p < h p := by
    intro x y hlt hyQ hf
    refine ⟨y - x, by omega, by omega, fun p hpP => ?_⟩
    have hdiv : (x * M % p) / h p = (y * M % p) / h p := congrFun (congrFun hf p) hpP
    have hp0 := hP p hpP
    refine near_zero (a := x * M % p) (b := y * M % p) (c := (y - x) * M % p) (Nat.mod_lt _ hp0) (Nat.mod_lt _ hp0) ?_ ?_ ?_
    · rw [← Nat.add_mod, ← add_mul, Nat.add_sub_cancel' hlt.le]
    · exact sub_lt_of_div_eq (hh p hpP) hdiv
    · exact sub_lt_of_div_eq (hh p hpP) hdiv.symm
  rcases Nat.lt_or_gt_of_ne hxy with hlt | hgt
  · exact key x y hlt (by have := mem_range.mp hy; omega) hfxy
  · exact key y x hgt (by have := mem_range.mp hx; omega) hfxy.symm

end Erdos1063.Box
