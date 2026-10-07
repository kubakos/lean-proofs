# Erdős #1063: `better_upper`

## Problem

From [erdosproblems.com/1063](https://www.erdosproblems.com/1063):

> Let $k\geq 2$ and define $n_k\geq 2k$ to be the least value of $n$ such that $n-i$
> divides $\binom{n}{k}$ for all but one $0\leq i<k$. Estimate $n_k$.

FC's `erdos_1063.better_upper` (category `research open` at FC commit `dbb5a211`) asks for
an upper bound better than Cambie's nₖ ≤ k·lcm(1, …, k−1): a function `upper_bound` with
nₖ = O(`upper_bound`) and `upper_bound` = o(k·lcm(1, …, k−1)).

## Result

```lean
theorem Erdos1063.Main.better_upper_explicit :
    Erdos1063.Statement (fun k => (2 : ℝ) ^ (k / 4))
```

That is, nₖ = O(2^⌊k/4⌋), and 2^⌊k/4⌋ = o(k·lcm(1, …, k−1)). `Erdos1063.Statement` is FC's
statement with `answer(sorry)` turned into the parameter `upper_bound` (`Statement.lean`,
transcribed from FC at `dbb5a21169ce4094913e6cad34faedd74df55157`).

`Erdos1063.Main.better_upper` proves the same statement with `upper_bound := n` itself. It
is formally valid but degenerate, and is not an answer; cite `better_upper_explicit`.

## Further results (statements not in FC)

**A subexponential upper bound.**

```lean
theorem Erdos1063.Subexp.n_le_exp_of_ge {k : ℕ} (hk : 2 ^ 64 ≤ k) :
    (n k : ℝ) ≤ Real.exp (100 * k * Real.log (Real.log k) / Real.log k)
```

`subexp_bound : SubexpBound` is the statement "there is an absolute constant C such that, for
all sufficiently large k, nₖ ≤ exp(C·k·log log k / log k)". That is the theorem P. White &
Claude claim (<https://github.com/pw/erdos1063-upper-bound>, commit `a28481f5`; the repository
says its construction was produced by GPT-5.6 Sol via Codex), and also
Cipollini's first bound. The proof uses the same construction and estimates as
`better_upper_explicit`, with a sharper last step. White & Claude's own argument, a
different construction, is not what is checked. `exp_littleO` gives nₖ = exp(o(k)). As an
estimate it is weak: with C = 100 it beats Cambie's bound only for k > 10²⁸¹, and 2^⌊k/4⌋
only for k > 10²¹³⁰.

**The structure of an admissible n, and a lower bound.** For every n ≥ 2k with exactly one
failing index e, and every pᵃ ∥ k:

- p^{a + v_p C(k−1,e) + ⌊log_p max(e, k−1−e)⌋} divides n − e (`Structure.pow_dvd_sub`);
- so e = n mod k (`eq_mod`), and n ≡ e (mod D(k, e)) (`D_dvd`);
- for a prime k/2 < p ≤ k, a lone multiple of p among n, …, n−k+1 is n − e (`wheel`);
- nₖ ≥ ∏_{pᵃ∥k} p^{a+⌊log_p(k−1)⌋} (`lower_bound`). This beats nₖ ≥ 2k only for composite
  k ≠ 4: `lower_bound_six` gives 72 ≤ n₆ ≤ 75.

The identity behind `pow_dvd_sub`, the facts e = n mod k and D(k, e) ∣ n − e, and the lower
bound come from rickyc's (R. Cipollini's) argument in the erdosproblems.com forum (2026-06-26
and 2026-07-10; AI-assisted, and the comment with the (k − 1) form says it was written by
GPT-5.6 Sol), which argues them for n = nₖ. jbell31 (2026-07-28, with AI assistance) stated
them for every solution, packaged the modulus as D(k, e), and added the wheel, a skip rule in
their search code ([`erdos1063_sweep.c`](https://github.com/Jaybell31/dreamwalk/blob/be54a5c39f69fd178ef153b9477bfead782d614d/erdos1063/erdos1063_sweep.c)), to make a search for nₖ, k ≤ 75, exhaustive.
`D_dvd` and `wheel` are the two mathematical facts that search's coverage argument uses; the
search's computation itself is not checked here.

## What this does not cover

- **Cipollini's sharp constant.** R. Cipollini, with GPT-5.6 Sol (2026-07-27, unreviewed,
  <https://www.overleaf.com/read/hrpsqsnqktky>), claims log nₖ ≤ (k / log k)(log log k +
  log log log k + log 2 + o(1)), using the prime number theorem, Mertens and Brun–Titchmarsh.
  The proofs here use his construction with elementary estimates instead (the primorial bound
  ∏_{p ≤ k} p ≤ 4ᵏ), which give exp(O(k log log k / log k)) with C = 100, not his constant.
- **Cipollini's lower bound** log nₖ ≥ c(log k)² (2026-08-04, unreviewed) is not formalised.
  Its proof uses the Baker–Harman theorem on primes in short intervals and Konyagin's estimate
  for rational points near a curve, which are not in Mathlib.
- **"Estimate nₖ" remains open:** the upper and lower bounds here are far apart.
- **Environment.** The proof is checked against a verbatim transcription of FC's statement
  under Mathlib `v4.35.0-rc3`, not inside FC's own environment.

## Checks on the statement

These show that the formal statement means what the problem says, and is not vacuous:

- `Gate.statement_iff`: (∃ `upper_bound`, `Statement upper_bound`) ↔ nₖ = o(k·lcm(1, …, k−1)).
- `Gate.n_two`, `Gate.n_three`, `Gate.n_four`: n₂ = 4, n₃ = 6, n₄ = 9, as in Guy, *Unsolved
  Problems in Number Theory*, B31.
- `Existence.two_mul_le_n`: the set defining nₖ is non-empty for every k ≥ 2, so nₖ ≥ 2k.
- `Existence.not_isLittleO_self`: the false variant nₖ = o(k) is refuted.
- `Main.not_statement_cambie`: Cambie's bound itself is not an answer, so "better" is a
  real requirement.

## Proof plan

Module docstrings refer to these steps. Notation: e < k, Q_e = k·C(k−1, e), v_p is the
p-adic valuation, and index i < k *fails* if (n − i) ∤ C(n, k).

1. *Carry criterion* (`Local`): by Kummer, v_p C(n, k) counts the a ≥ 1 with
   n mod pᵃ < k mod pᵃ; index i fails iff some p has v_p(n − i) > v_p C(n, k).
2. *Stabilization* (`Local`): if n = e + N with v_p(N) large, v_p C(n, k) = v_p(N) − v_p(Q_e),
   so p can block only index e.
3. *One carry* (`Local`): if p² > k and n mod p < k mod p, p blocks no index.
4. *Modulus* (`Construction`): M = Q_e² · ∏_{p ≤ 2e} p^(⌊log_p k⌋ + 1).
5. *Lucas* (`Local`): for primes p ∈ (2e, k] not dividing Q_e, k mod p > e.
6. *Box principle* (`Box`): some 1 ≤ t ≤ ∏_{p} ⌈p / h_p⌉ puts t·M mod p within h_p of 0
   for every such p, where h_p = min(e, k mod p − e).
7. *Admissibility* (`Existence`, `Construction`): n = e + M·t has exactly one failing index,
   e, so nₖ ≤ e + M·Q.
8. *Sizes* (`Estimates`): M ≤ k^(6e+4) and Q ≤ ⌈k/e⌉^|P| · kᵉ, with (2e)^|P| ≤ 4ᵏ.
9. *Asymptotic* (`Asymptotic`, `Main`): with L = ⌊log₂ k⌋ and e = ⌊k / L²⌋, eventually
   nₖ ≤ 2^⌊k/4⌋, and k·lcm(1, …, k−1) ≥ 2^(k−1) (Mathlib's `Chebyshev.two_pow_le_mul_lcmUpto`).

## Files

| File | Contents |
|---|---|
| `Statement.lean` | FC's statement, generated by `tools/fc_statement.py` |
| `StatementGate.lean` | `statement_iff`, small values |
| `Local.lean` | steps 1–3 and 5 |
| `Existence.lean` | step 7's glue, a crude existence bound, nₖ ≥ 2k, the false variant |
| `Box.lean` | step 6 |
| `Construction.lean` | steps 4 and 7 |
| `Estimates.lean` | step 8 |
| `Asymptotic.lean` | step 9, from an exponential bound to FC's little-o |
| `Main.lean` | the main theorem |
| `Subexp.lean` | the subexponential bound |
| `Structure.lean` | the structure of an admissible n, the lower bound |
