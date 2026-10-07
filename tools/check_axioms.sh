#!/usr/bin/env bash
# The referee. A result counts in this repo only if every axiom it rests on is one of
# Lean's standard three: propext, Classical.choice, Quot.sound.
#
#     tools/check_axioms.sh <Module> <decl> [<decl> ...]
#         e.g. tools/check_axioms.sh Research.Basic Research.Basic.sanity
#     tools/check_axioms.sh --self-test     # prove the check can fail
#
# What it rejects, and why each is not a proof here:
#   sorryAx              a `sorry` or `admit` somewhere in the dependency tree
#   native_decide        trusts the compiler, not the kernel. On Lean 4.35 it shows as
#                        `<decl>._native.native_decide.ax_N_M`; older toolchains showed
#                        Lean.ofReduceBool. The allowlist catches every form.
#   any declared `axiom` an assumption, not a result
#
# It is an ALLOWLIST on purpose: it names the three axioms that are acceptable, never the
# ones that are not, so a new form of unsoundness is rejected without anyone predicting it.
#
# It does NOT check that the statement says what the problem says. A clean result for a
# misformalized statement is worthless; checking the statement is a separate step, not this.
#
# Exit 0 only if every named declaration was found and judged clean. A declaration that
# produces no verdict is a failure: a check that did not run must not pass.
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
ALLOWED=" propext Classical.choice Quot.sound "
TMP="$REPO/.lake/check_axioms"     # .lake/ is gitignored build output
mkdir -p "$TMP"

# judge <lean-file> <decl>...  — compile the file, then judge each decl's axiom line.
judge() {
    local file="$1"; shift
    local out
    if ! out="$("$REPO/tools/lake" env lean "$file" 2>&1)"; then
        printf '%s\n' "$out" >&2
        echo "  FAIL  the check file did not compile (unknown module or declaration?)"
        return 1
    fi
    local rc=0 decl line axioms bad a
    for decl in "$@"; do
        # `#print axioms` prints one of:
        #   'X' depends on axioms: [a, b, c]
        #   'X' does not depend on any axioms
        line="$(grep -F "'$decl' " <<<"$out" | grep -E "depends on axioms|does not depend on any axioms" | head -1 || true)"
        if [[ -z "$line" ]]; then
            echo "  FAIL  $decl — no verdict produced"; rc=1; continue
        fi
        if [[ "$line" == *"does not depend on any axioms"* ]]; then
            echo "  ok    $decl — no axioms"; continue
        fi
        axioms="$(sed -n 's/.*depends on axioms: \[\(.*\)\].*/\1/p' <<<"$line")"
        bad=""
        for a in ${axioms//,/ }; do
            [[ "$ALLOWED" == *" $a "* ]] || bad="$bad $a"
        done
        if [[ -n "$bad" ]]; then
            echo "  FAIL  $decl — rests on:$bad"; rc=1
        else
            echo "  ok    $decl — [$axioms]"
        fi
    done
    return $rc
}

if [[ "${1:-}" == "--self-test" ]]; then
    # Fixtures with known verdicts. The self-test passes only if every verdict matches,
    # so a judge that passes everything (or nothing) fails here. The long axiom name
    # checks that a wrapped output line is not silently misread.
    F="$TMP/selftest.lean"
    cat > "$F" <<'EOF'
set_option format.width 100000
theorem st_none : 2 + 2 = 4 := rfl
theorem st_choice : ∀ p : Prop, p ∨ ¬p := Classical.em
theorem st_sorry : 1 = 2 := sorry
axiom st_a_deliberately_long_axiom_name_to_test_that_long_lines_are_not_misread_by_the_parser : False
theorem st_axiom : 1 = 2 := st_a_deliberately_long_axiom_name_to_test_that_long_lines_are_not_misread_by_the_parser.elim
theorem st_native : 2 + 2 = 4 := by native_decide
#print axioms st_none
#print axioms st_choice
#print axioms st_sorry
#print axioms st_axiom
#print axioms st_native
EOF
    want_ok="st_none st_choice"; want_fail="st_sorry st_axiom st_native"
    result="$(judge "$F" $want_ok $want_fail || true)"
    printf '%s\n' "$result"
    st=0
    for d in $want_ok;   do grep -qE "^  ok    $d " <<<"$result"   || { echo "SELF-TEST: $d should pass"; st=1; }; done
    for d in $want_fail; do grep -qE "^  FAIL  $d " <<<"$result" || { echo "SELF-TEST: $d should fail"; st=1; }; done
    (( st == 0 )) && echo "self-test OK: the referee accepts clean proofs and rejects sorry, axioms, native_decide."
    exit $st
fi

if (( $# < 2 )); then
    sed -n '2,20p' "$0" >&2
    exit 2
fi
MODULE="$1"; shift
F="$TMP/check.lean"
{
    echo "import $MODULE"
    echo "set_option format.width 100000"
    for d in "$@"; do echo "#print axioms $d"; done
} > "$F"
judge "$F" "$@"
