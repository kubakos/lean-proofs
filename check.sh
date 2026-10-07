#!/usr/bin/env bash
# Check every published result:
#   1. Palomar's source rules: every .lean file starts with a `module` header and has at most
#      10,000 lines; Challenge.lean has at most 1,000 lines and 100 KiB; no .lean symlinks;
#   2. build every target (Research, Challenge, Solution);
#   3. the axiom check's self-test, which shows it rejecting sorry, a declared axiom and
#      native_decide, then the axiom check on every theorem in referee.txt;
#   4. the statement-transcription self-test and pinned check: each Research/*/Statement.lean
#      must be byte-identical to what tools/fc_statement.py generates from formal-conjectures
#      at the commit recorded in its header;
#   5. Comparator, as Palomar runs it: Solution's theorems have exactly Challenge's types, every
#      constant they use (Erdos1063.n, Erdos1063.Statement, Mathlib) is identical, only the three
#      standard axioms are used, and the proofs replay in the toolchain's NanoDa and con-ron
#      kernels. Needs bwrap, or CHECK_NO_SANDBOX=1 (below). (Palomar itself builds the Challenge before the Solution in a
#      sandbox; this local run builds everything first, so it is a preflight, not a substitute.)
# Exits non-zero on the first failure. Needs elan in .elan/ (see README).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
FC=.cache/formal-conjectures
if [[ ! -d "$FC/.git" ]]; then
    git clone -q https://github.com/google-deepmind/formal-conjectures.git "$FC"
fi

python3 - <<'PY'
import os, re, sys
bad = []
for root, dirs, files in os.walk("."):
    dirs[:] = [d for d in dirs if d not in (".git", ".lake", ".elan", ".cache")]
    for f in files:
        if not f.endswith(".lean"):
            continue
        p = os.path.join(root, f)
        if os.path.islink(p):
            bad.append(f"{p}: .lean symlink"); continue
        t = open(p, encoding="utf-8").read()
        lines = t.count("\n") + int(bool(t) and not t.endswith("\n"))
        if lines > 10000:
            bad.append(f"{p}: {lines} lines > 10000")
        # the first command after whitespace, `--` comments and plain `/- -/` comments
        head = re.sub(r"\A(?:\s+|--[^\n]*\n|/-(?![-!]).*?-/)*", "", t, flags=re.S)
        if not re.match(r"module(?![\w.'])", head):
            bad.append(f"{p}: no `module` header")
c = open("Challenge.lean", encoding="utf-8").read()
cl = c.count("\n") + int(bool(c) and not c.endswith("\n"))
if cl > 1000 or len(c.encode()) > 100 * 1024:
    bad.append(f"Challenge.lean: {cl} lines, {len(c.encode())} bytes (limits 1000 lines, 100 KiB)")
for b in bad:
    print("source rule:", b)
if bad:
    sys.exit(1)
print("source rules: ok")
PY

tools/lake build
tools/check_axioms.sh --self-test
n=0
while read -r module decls; do
    [[ -z "$module" || "$module" == \#* ]] && continue
    # shellcheck disable=SC2086  # one declaration per word
    tools/check_axioms.sh "$module" $decls
    n=$((n + 1))
done < referee.txt
(( n > 0 )) || { echo "check.sh: referee.txt names no theorem" >&2; exit 1; }
python3 tools/fc_statement.py --self-test
for f in Research/*/Statement.lean; do
    python3 tools/fc_statement.py check "$f"
done

# CHECK_NO_SANDBOX=1 runs Comparator without its bwrap sandbox. The sandbox contains an
# untrusted Solution; drop it only for your own code, on a machine where bwrap cannot create a
# user namespace (Ubuntu 24.04's AppArmor default). The judgement itself is the same. CI keeps
# the sandbox.
sandbox=()
if [[ "${CHECK_NO_SANDBOX:-}" == 1 ]]; then
    sandbox=(--inadvisably-no-sandbox)
    echo "check.sh: CHECK_NO_SANDBOX=1, Comparator runs without its sandbox"
else
    command -v bwrap >/dev/null || { echo "check.sh: bwrap is needed for lake comparator" >&2; exit 1; }
fi
prefix="$(tools/lake env lean --print-prefix)"
config="$(mktemp "${TMPDIR:-/tmp}/comparator.XXXXXX.json")"
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json, sys
src, dst, prefix = sys.argv[1:]
cfg = json.load(open(src, encoding="utf-8"))
cfg.pop("enable_nanoda", None)
cfg["external_kernels"] = {"nanoda": [f"{prefix}/bin/nanoda_bin"],
                           "con-ron": [f"{prefix}/bin/con-ron"]}
json.dump(cfg, open(dst, "w", encoding="utf-8"), indent=2)
PY
tools/lake comparator --config "$config" "${sandbox[@]}"
echo "check.sh: all published results check."
