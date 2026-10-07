# lean-proofs

Lean 4 proofs of statements from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (FC).

Every theorem listed in `referee.txt` is checked by Lean's kernel and rests only on Lean's
three standard axioms (`propext`, `Classical.choice`, `Quot.sound`): no `sorry`, no
`native_decide`, no declared `axiom`. `./check.sh` verifies this, and CI runs it on every
push.

## Results

| Problem | Lean theorems (`Challenge.lean`) | Result | Details |
|---|---|---|---|
| [Erdős #1063](https://www.erdosproblems.com/1063) | `Erdos1063.Results.better_upper` | FC's `erdos_1063.better_upper` with answer 2^⌊k/4⌋ | [Research/Erdos1063](Research/Erdos1063/README.md) |
| | `subexp_bound`, `n_le_exp_of_ge`, `exp_littleO` | nₖ ≤ exp(C·k·log log k / log k); C = 100 for k ≥ 2⁶⁴; nₖ = exp(o(k)) | same |
| | `eq_mod_and_dvd`, `wheel`, `lower_bound` | structure of every admissible n; nₖ ≥ ∏_{pᵃ∥k} p^{a+⌊log_p(k−1)⌋} | same |

Published versions will be tagged (for example `erdos-1063-v1`); links to a proof cite a commit.

## How the statements are copied

Each problem's `Statement.lean` is generated from FC's file at a pinned commit by
`tools/fc_statement.py`, never written by hand. Every definition, `open` and `namespace` in
scope for FC's statement is copied verbatim and in order, and FC's `answer(sorry)`
placeholder becomes a parameter of `def Statement` (or FC's proposition becomes
`def Statement : Prop`). `tools/fc_statement.py check` regenerates the file from FC and
compares it byte for byte, so the statement proved here is FC's text.

One difference remains: the statement is elaborated against this repo's Mathlib
(`lakefile.toml`, `lake-manifest.json`), not inside FC's own environment.

## Palomar layout

`Challenge.lean` is the statement of record: it imports Mathlib only, carries a verbatim copy of
FC's definitions, and states each result with `sorry`. `Solution.lean` restates the same theorems
with the same names and proves them from `Research/`. `comparator.json` lists them, and
[Comparator](https://github.com/leanprover/comparator) checks that the types match, that every
constant they use is identical on both sides, and that only the three standard axioms are used.
`formalization.yaml` records sources, provenance, authorship and AI involvement.

## Checking

Needs git, curl, python3 (standard library only) and, for Comparator, `bwrap` (bubblewrap).
The scripts expect elan in `.elan/`:

```sh
curl -sSfL https://raw.githubusercontent.com/leanprover/elan/v4.2.4/elan-init.sh -o elan-init.sh
ELAN_HOME="$PWD/.elan" sh elan-init.sh -y --default-toolchain none --no-modify-path
tools/lake exe cache get      # Mathlib's prebuilt cache
./check.sh                    # source rules, build, axiom check, statement check, Comparator
```

- `tools/lake` runs lake from `.elan/`.
- `tools/check_axioms.sh <Module> <declaration>...` is the axiom check. It is an allowlist of
  the three standard axioms; `tools/check_axioms.sh --self-test` shows it rejecting `sorry`,
  a declared axiom and `native_decide`.
- `tools/fc_statement.py --self-test` shows the statement check rejecting altered copies.

## How these proofs were made

The proofs were written by an AI agent (Claude, by Anthropic) in Claude Code, working under
the direction of the repository owner, who chose the problems and decides what is published
here. No human mathematician has reviewed the proofs; Lean's kernel checks them. Each problem's
README credits the mathematics the proof builds on, and says what the result does not
cover.

## Licence

Apache-2.0 (`LICENSE`). `Challenge.lean` and the `Statement.lean` files contain text copied from
formal-conjectures (Copyright 2026 The Formal Conjectures Authors, Apache-2.0); its notice is
kept in each file.
