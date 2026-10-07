"""ADR 0002: verbatim transcription of formal-conjectures (FC) statements, and its checks.

    .venv/bin/python tools/fc_statement.py render PATH THEOREM [--sha SHA] > Research/<Slug>/Statement.lean
        generate the transcription file (the only way to produce one)
    .venv/bin/python tools/fc_statement.py check FILE [--no-lean]
        PINNED check: FILE is byte-identical to what `render` produces from FC at the SHA
        in FILE's header; then (unless --no-lean) FILE compiles, its statement rests on the
        standard axioms only, and no constant it uses is one FC defines in its own
        helper libraries (where our Mathlib-only file would resolve a different constant)
    .venv/bin/python tools/fc_statement.py drift FILE [--ref REF] [--fetch]
        DRIFT check: would `render` at REF (default origin/main) produce the same file body?
    .venv/bin/python tools/fc_statement.py --self-test [--no-lean]

FC is read as text from the clone at .cache/formal-conjectures (gitignored) with
`git show SHA:PATH`. FC code is never built or run here.

## What `render` produces (and therefore what `check` accepts)

There are no hand-written parts. From FC's file at the pinned commit:

  1. a fixed header recording `fc-sha`, `fc-path`, `fc-theorem`, `fc-category`, `fc-shape`
     and FC's licence notice;
  2. `module`, `public import Mathlib` and `@[expose] public section`, fixed text: the
     public repo must use Lean's module system (ADR 0003, Palomar), and exposing the copied
     definitions keeps their bodies visible to importers, as FC does;
  3. every blank-line-delimited block of FC's file that comes before the target theorem,
     verbatim and in order, except FC's licence block, `module` / `import` /
     `public import` lines, `@[expose] public section`, and theorem/lemma blocks. So every
     definition, `open`, `namespace`, `variable`, `instance` and `notation` that is in scope
     for FC's statement is in scope here, in the same order;
  4. the statement, with FC's answer placeholder removed:
       shape `iff`: FC `theorem T : answer(sorry) ↔ P` becomes `def Statement : Prop :=` and P;
       shape `let`: FC `theorem T : let X : τ := answer(sorry)` followed by Q becomes
                    `def Statement (X : τ) : Prop :=` and Q.
     Every line of P or Q keeps its original column. Other shapes and theorems with binders
     are rejected, not guessed at;
  5. `end` lines closing the namespaces and sections opened in step 3.

A block of step 3 that mixes a theorem with anything else, or a generated file that
contains `answer(`, or the words `sorry`/`admit`/`axiom`/`native_decide` in code, fails
closed.

Residual risks, which this tool cannot see, are checked by gate 3's small-instance and
false-variant proofs: FC elaborates against Mathlib v4.33.1 plus its own helper libraries,
and we elaborate against our Mathlib. Instances or notation that FC's helpers provide are
not reproduced. If a statement needs them, it either fails to compile here, which is loud,
or picks up a different instance, which is silent and is what gate 3's proofs are for.

Exit status: 0 pass (drift: no drift); 1 fail (drift: drift found); 2 usage/environment.
"""

import difflib
import os
import re
import subprocess
import sys
import tempfile

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FC_DEFAULT = os.path.join(REPO, ".cache", "formal-conjectures")
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
FORBIDDEN_CODE = ["sorry", "admit", "axiom", "native_decide"]
FC_HELPER_DIRS = ["FormalConjecturesForMathlib", "FormalConjecturesUtil",
                  "FormalConjectures/ForMathlib", "FormalConjectures/Util"]


class CheckError(Exception):
    """A check that cannot produce a pass verdict (fail closed)."""


# ---------------------------------------------------------------- reading FC

def git(fc, *args):
    r = subprocess.run(["git", "-C", fc, *args], capture_output=True, text=True)
    if r.returncode != 0:
        raise CheckError(f"git {' '.join(args)} failed in {fc}: {r.stderr.strip()}")
    return r.stdout


def fc_show(fc, ref, path):
    return git(fc, "show", f"{ref}:{path}")


def fc_resolve(fc, ref):
    return git(fc, "rev-parse", "--verify", f"{ref}^{{commit}}").strip()


# ---------------------------------------------------------------- statement extraction

OPEN = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "⦃": "⦄"}
CLOSE = set(OPEN.values())


def _scan(text, start, stop_at):
    """Scan Lean source from `start`, skipping comments and strings, tracking bracket depth.

    stop_at == ':'  -> index of the first depth-0 ':' that is not part of ':='.
    stop_at == ':=' -> index of the first depth-0 ':=' not consumed by a pending depth-0
                       `let`/`have` (the end of a theorem statement).
    """
    depth, pending, i, n = 0, 0, start, len(text)
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            i = text.find("\n", i)
            i = n if i < 0 else i
            continue
        if text.startswith("/-", i):
            j = text.find("-/", i + 2)
            if j < 0:
                raise CheckError("unterminated block comment")
            i = j + 2
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            i = j + 1
            continue
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth < 0:
                raise CheckError("unbalanced brackets in statement")
        elif depth == 0:
            if stop_at == ":=" and re.match(r"(let|have)\b", text[i:]) and \
                    (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_.'")):
                pending += 1
            elif text.startswith(":=", i):
                if stop_at == ":=":
                    if pending:
                        pending -= 1
                        i += 2
                        continue
                    return i
                i += 2
                continue
            elif c == ":" and stop_at == ":":
                return i
        i += 1
    raise CheckError(f"no top-level {stop_at!r} found")


def find_theorem(text, theorem):
    m = re.search(r"^(?:theorem|lemma)\s+" + re.escape(theorem) + r"(?=[\s:({\[⦃])", text, re.M)
    if not m:
        raise CheckError(f"theorem {theorem} not found (a check that produced no verdict)")
    return m


def extract(text, theorem):
    """(binders, statement, statement_start_index) of `theorem` in FC source `text`."""
    m = find_theorem(text, theorem)
    colon = _scan(text, m.end(), ":")
    binders = text[m.end():colon].strip()
    end = _scan(text, colon + 1, ":=")
    raw = text[colon + 1:end]
    lead = len(raw) - len(raw.lstrip())
    return binders, raw.strip(), colon + 1 + lead


def normalize(statement):
    """(shape, fields) with the answer placeholder removed; `body_offset` locates the body."""
    m = re.fullmatch(r"(answer\(sorry\)\s*↔\s*)(.*)", statement, re.S)
    if m:
        return "iff", {"body": m.group(2).strip(), "body_offset": len(m.group(1))}
    m = re.fullmatch(r"(let\s+([^\s:]+)\s*:\s*(.+?)\s*:=\s*answer\(sorry\)\s*\n)(.*)", statement, re.S)
    if m:
        rest = m.group(4)
        lead = len(rest) - len(rest.lstrip())
        return "let", {"name": m.group(2), "type": m.group(3), "body": rest.strip(),
                       "body_offset": len(m.group(1)) + lead}
    raise CheckError("unsupported statement shape (only `answer(sorry) ↔ P` and "
                     "`let X : τ := answer(sorry)` are transcribed); statement begins: "
                     + statement[:80].replace("\n", " "))


def category_of(text, theorem):
    cat = re.search(r"@\[category ([^,\]]+)[^\]]*\]\s*\n\s*(?:theorem|lemma) "
                    + re.escape(theorem) + r"(?=[\s:({\[⦃])", text)
    if not cat:
        raise CheckError(f"no @[category …] attribute found directly above {theorem}")
    return cat.group(1).strip()


# ---------------------------------------------------------------- rendering

THEOREM_LINE = re.compile(r"^(?:(?:private|protected)\s+)?(?:theorem|lemma|example)\b", re.M)
DECL_LINE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*"
                       r"(?:def|abbrev|instance|structure|class|inductive|notation|infix|infixl|infixr|"
                       r"prefix|postfix|macro|syntax|open|variable|namespace|section|end|set_option|"
                       r"attribute|local|scoped|opaque|axiom)\b", re.M)


def code_of(text):
    """Lean source with (nested) block comments and line comments replaced by spaces."""
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if not depth and text.startswith("--", i):
            j = text.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(text[i] if not depth or text[i] == "\n" else " ")
        i += 1
    if depth:
        raise CheckError("unterminated block comment")
    return "".join(out)


def split_blocks(text):
    """[(start_index, block_text)]: blocks separated by blank lines that are outside comments."""
    blocks, start, pos, depth = [], None, 0, 0
    for line in text.split("\n"):
        if line.strip() == "" and depth == 0:
            if start is not None:
                blocks.append((start, text[start:pos].rstrip("\n")))
                start = None
        elif start is None:
            start = pos
        i = 0                                      # update block-comment depth across this line
        while i < len(line):
            if line.startswith("/-", i):
                depth, i = depth + 1, i + 2
            elif depth and line.startswith("-/", i):
                depth, i = depth - 1, i + 2
            elif not depth and line.startswith("--", i):
                break
            else:
                i += 1
        pos += len(line) + 1
    if depth:
        raise CheckError("unterminated block comment")
    if start is not None:
        blocks.append((start, text[start:].rstrip("\n")))
    return blocks


def is_excluded(block):
    code = code_of(block)
    lines = [l.strip() for l in code.split("\n") if l.strip()]
    if not lines:
        return None                                # a pure comment block: copied, harmless
    if all(l == "module" or re.match(r"(public\s+)?import\s", l) for l in lines):
        return "imports"
    if all(re.fullmatch(r"(@\[expose\]\s*)?public\s+section", l) for l in lines):
        return "module-section"
    if THEOREM_LINE.search(code):
        if DECL_LINE.search(code):
            raise CheckError("a block mixes a theorem with other declarations; refusing to "
                             "guess what to copy:\n" + block[:300])
        return "theorem"
    return None


def scopes_opened(blocks):
    """Namespaces/sections still open after the given blocks, innermost last."""
    stack = []
    for b in blocks:
        for line in code_of(b).split("\n"):
            s = line.strip()
            m = re.match(r"namespace\s+(\S+)\s*$", s)
            if m:
                stack.append(("namespace", m.group(1)))
                continue
            m = re.match(r"(?:noncomputable\s+)?section(?:\s+(\S+))?\s*$", s)
            if m:
                stack.append(("section", m.group(1) or ""))
                continue
            m = re.match(r"end(?:\s+(\S+))?\s*$", s)
            if m:
                if not stack:
                    raise CheckError(f"unmatched `{s}` in copied blocks")
                kind, name = stack.pop()
                if (m.group(1) or "") != name:
                    raise CheckError(f"`{s}` closes {kind} {name!r}")
    return stack


def licence_text(text):
    m = re.match(r"\s*/-(.*?)-/", text, re.S)
    if not m or "License" not in m.group(1):
        raise CheckError("FC file has no licence block at the top")
    return "\n".join("  " + l.strip() if l.strip() else "" for l in m.group(1).strip().split("\n"))


def render(fc, sha, path, theorem):
    """(full_text, body_text, decl_name) of the transcription file."""
    sha = fc_resolve(fc, sha)
    text = fc_show(fc, sha, path)
    binders, statement, st_idx = extract(text, theorem)
    if binders:
        raise CheckError(f"{theorem} has binders {binders!r}; transcription of binders is not supported")
    shape, fields = normalize(statement)
    category = category_of(text, theorem)
    thm_start = find_theorem(text, theorem).start()

    blocks = []
    for k, (start, block) in enumerate(split_blocks(text)):
        if start >= thm_start:
            break
        if is_excluded(block) is None:
            blocks.append(block)
    scopes = scopes_opened(blocks)
    ns = ".".join(name for kind, name in scopes if kind == "namespace" and name)

    body_start = st_idx + fields["body_offset"]
    col = body_start - (text.rfind("\n", 0, body_start) + 1)
    body_lines = fields["body"].split("\n")
    body = " " * col + body_lines[0] + ("\n" + "\n".join(body_lines[1:]) if len(body_lines) > 1 else "")
    if shape == "iff":
        def_line = "def Statement : Prop :="
    else:
        def_line = f"def Statement ({fields['name']} : {fields['type']}) : Prop :="
    ends = [f"end {name}".rstrip() for kind, name in reversed(scopes)]

    header = f"""/-
`{theorem}`, transcribed verbatim from google-deepmind/formal-conjectures
by tools/fc_statement.py (ADR 0002). Generated file: do not edit. Regenerate with
  .venv/bin/python tools/fc_statement.py render {path} {theorem} --sha {sha}

fc-sha: {sha}
fc-path: {path}
fc-theorem: {theorem}
fc-category: {category}
fc-shape: {shape}

Everything after `@[expose] public section` is copied from that file at that commit, except
the line `{def_line}` and the closing `end` lines. A claim about this problem is
`{(ns + '.') if ns else ''}Statement` or its negation. Copied text:
{licence_text(text)}
-/
module

public import Mathlib

@[expose] public section
"""
    body_text = "\n\n".join(blocks + [def_line + "\n" + body] + (["\n".join(ends)] if ends else [])) + "\n"
    full = header + "\n" + body_text
    if "answer(" in full:
        raise CheckError("rendered file would contain `answer(`")
    code = re.sub(r"--[^\n]*", " ", re.sub(r"/-.*?-/", " ", body_text, flags=re.S))
    for tok in FORBIDDEN_CODE:
        if re.search(r"(?<![\w.'])" + re.escape(tok) + r"(?![\w'])", code):
            raise CheckError(f"copied FC text contains {tok!r} in code; refusing to transcribe")
    decl = (ns + ".Statement") if ns else "Statement"
    return full, body_text, decl


def header_field(text, key):
    m = re.search(r"^" + re.escape(key) + r":\s*(\S.*?)\s*$", text, re.M)
    if not m:
        raise CheckError(f"header field {key} missing")
    return m.group(1)


# ---------------------------------------------------------------- FC helper-library names

def fc_helper_names(fc, sha):
    """Fully qualified names of declarations in FC's helper libraries at `sha` (best effort)."""
    files = [f for f in git(fc, "ls-tree", "-r", "--name-only", sha).split("\n")
             if f.endswith(".lean") and any(f.startswith(d + "/") or f == d + ".lean" for d in FC_HELPER_DIRS)]
    names = set()
    decl = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|"
                      r"nonrec|public|meta)\s+)*(?:def|abbrev|theorem|lemma|structure|class|inductive|"
                      r"instance|opaque|axiom)\s+([^\s:({\[⦃]+)")
    for f in files:
        stack = []
        for line in fc_show(fc, sha, f).split("\n"):
            s = line.strip()
            m = re.match(r"namespace\s+(\S+)", s)
            if m:
                stack.append(m.group(1))
                continue
            if re.match(r"(?:noncomputable\s+)?section\b", s):
                stack.append(None)
                continue
            if re.match(r"end\b", s) and stack:
                stack.pop()
                continue
            m = decl.match(line)
            if m:
                name = m.group(1)
                if name.startswith("_root_."):
                    names.add(name[len("_root_."):])
                else:
                    prefix = ".".join(x for x in stack if x)
                    names.add((prefix + "." if prefix else "") + name)
    return names


# ---------------------------------------------------------------- Lean step

LEAN_PROBE = """
set_option format.width 100000
#print axioms {decl}
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut todo : Array Name := #[`{decl}]
  let mut seen : NameSet := {{}}
  while todo.size > 0 do
    let c := todo.back!
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    match env.getModuleIdxFor? c with
    | some _ => IO.println s!"FCEXT {{c}}"
    | none =>
      if let some ci := env.find? c then
        for d in ci.type.getUsedConstants do todo := todo.push d
        if let some v := ci.value? then
          for d in v.getUsedConstants do todo := todo.push d
"""


def lean_step(path, decl, fc, sha):
    """Compile FILE itself, judge the statement's axioms, and look for helper-name collisions."""
    problems = []
    work = os.path.join(REPO, ".lake", "fc_statement")
    os.makedirs(work, exist_ok=True)
    probe = os.path.join(work, "probe.lean")
    with open(probe, "w", encoding="utf-8") as fh:
        fh.write(open(path, encoding="utf-8").read() + LEAN_PROBE.format(decl=decl))
    r = subprocess.run([os.path.join(REPO, "tools", "lake"), "env", "lean", probe],
                       capture_output=True, text=True, cwd=REPO)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        return [f"the file does not compile:\n{out[-3000:]}"]
    line = next((l for l in out.split("\n") if f"'{decl}'" in l and
                 ("depends on axioms" in l or "does not depend on any axioms" in l)), None)
    if line is None:
        return [f"no axiom verdict produced for {decl}"]
    m = re.search(r"depends on axioms: \[(.*)\]", line)
    bad = sorted(set(a.strip() for a in m.group(1).split(",")) - ALLOWED_AXIOMS) if m else []
    if bad:
        problems.append(f"{decl} rests on non-standard axioms: {bad}")
    used = {l.split()[1] for l in out.split("\n") if l.startswith("FCEXT ")}
    if not used:
        problems.append("no external constants listed; the collision probe did not run")
    clash = sorted(used & fc_helper_names(fc, sha))
    if clash:
        problems.append(f"{decl} uses constants that FC defines in its helper libraries, which "
                        f"this Mathlib-only file resolves elsewhere: {clash}")
    return problems


# ---------------------------------------------------------------- check / drift

def run_check(path, lean=True, fc=FC_DEFAULT):
    text = open(path, encoding="utf-8").read()
    sha = header_field(text, "fc-sha")
    if not re.fullmatch(r"[0-9a-f]{40}", sha):
        raise CheckError(f"fc-sha must be a full 40-hex commit id, got {sha!r}")
    want, _, decl = render(fc, sha, header_field(text, "fc-path"), header_field(text, "fc-theorem"))
    if text != want:
        diff = "".join(list(difflib.unified_diff(want.splitlines(True), text.splitlines(True),
                                                 "rendered", "file", n=1))[:40])
        return [f"file differs from the rendering at {sha[:8]}:\n{diff}"]
    if lean:
        return lean_step(path, decl, fc, sha)
    return []


def run_drift(path, ref, fc=FC_DEFAULT):
    text = open(path, encoding="utf-8").read()
    sha, fpath, thm = (header_field(text, k) for k in ("fc-sha", "fc-path", "fc-theorem"))
    pinned, pinned_body, _ = render(fc, sha, fpath, thm)
    if text != pinned:
        return ["file is not pinned-clean; run `check` first"], sha
    at = fc_resolve(fc, ref)
    try:
        full, body, _ = render(fc, at, fpath, thm)
    except CheckError as e:
        return [f"cannot render at {ref} ({at[:8]}): {e}"], at
    problems = []
    if body != pinned_body:
        diff = "".join(list(difflib.unified_diff(pinned_body.splitlines(True), body.splitlines(True),
                                                 f"pinned {sha[:8]}", f"{ref} {at[:8]}", n=1))[:40])
        problems.append(f"copied text changed upstream:\n{diff}")
    for key in ("fc-category", "fc-shape"):
        if header_field(full, key) != header_field(pinned, key):
            problems.append(f"{key} changed upstream: {header_field(pinned, key)!r} -> {header_field(full, key)!r}")
    return problems, at


# ---------------------------------------------------------------- self-test

SHA_HEAD = "dbb5a21169ce4094913e6cad34faedd74df55157"   # 2026-10-06
SHA_261_OLD = "da642c0e"                                  # 261 added, 2026-09-02
SHA_261_NEW = "a56710a5"                                  # two_representations solved, 2026-09-27
P261 = "FormalConjectures/ErdosProblems/261.lean"


def self_test(lean=True):
    results = []

    def expect(name, ok_expected, fn, why=None):
        try:
            problems = fn()
            ok = not problems
            detail = "" if ok else problems[0]
        except CheckError as e:
            ok, detail = False, str(e)
        right_reason = ok or why is None or why in detail
        passed = ok == ok_expected and right_reason
        results.append(passed)
        print(f"  {'pass' if passed else 'WRONG'}  [{'ok  ' if ok else 'FAIL'} expected "
              f"{'ok' if ok_expected else 'FAIL'}] {name}"
              f"{(' — ' + detail.split(chr(10))[0][:100]) if detail else ''}"
              f"{'' if right_reason else '  (failed for the wrong reason; wanted: ' + why + ')'}")

    fc = FC_DEFAULT
    with tempfile.TemporaryDirectory() as d:
        def fixture(name, content):
            p = os.path.join(d, name)
            open(p, "w", encoding="utf-8").write(content)
            return p

        good, _, decl = render(fc, SHA_HEAD, P261, "erdos_261.parts.ii")
        expect("rendered 261 parts.ii passes the pinned check", True,
               lambda: run_check(fixture("good.lean", good), lean=False))

        # One mutation per finding of the 2026-10-06 skeptic review, plus the earlier fixtures.
        mutations = [
            ("statement token changed (n > 0 -> n ≥ 0)", ("∀ n > 0", "∀ n ≥ 0")),
            ("helper weakened (t ≥ 2 -> t ≥ 1)  [F1]", ("(t ≥ 2)", "(t ≥ 1)")),
            ("helper truncated (last conjunct dropped)",
             (" ∧\n  (1 ≤ a) ∧ n / (2 ^ n : ℚ) = ∑ k, (a k) / (2 ^ (a k) : ℚ)", "")),
            ("shadowing helper added in the namespace  [F2]",
             ("def Statement : Prop :=", "def Erdos261Prop' (n : ℕ) : Prop := 0 < n\n\ndef Statement : Prop :=")),
            ("statement renamed, decoy `Statement := True` added  [F3]",
             ("def Statement : Prop :=", "def Statement : Prop := True\n\ndef StatementFC : Prop :=")),
            ("comment swallows the real statement  [F4]",
             ("def Statement : Prop :=", "def Statement : Prop := True /- : Prop :=")),
            ("optional-parameter binder  [F5]",
             ("def Statement : Prop :=", "def Statement (Erdos261Prop : ℕ → Prop := fun _ => True) : Prop :=")),
            ("local instance before the statement  [F6]",
             ("def Statement : Prop :=",
              "local instance (priority := high) badLT : LT ℕ := ⟨fun _ _ => False⟩\n\ndef Statement : Prop :=")),
            ("instance before the copied blocks  [F7]",
             ("import Mathlib\n",
              "import Mathlib\n\ninstance (priority := high) badLE {t : ℕ} : LE (Fin t → ℕ) := ⟨fun _ _ => True⟩\n")),
            ("public import outside Mathlib  [F8b]",
             ("import Mathlib\n", "import Mathlib\npublic import Batteries.Data.List.Basic\n")),
            ("comment-led continuation after the statement  [F11]",
             ("\n\nend Erdos261", "\n-- (FC text ends here)\n  ∨ True\n\nend Erdos261")),
            ("`1 ≤ a` dropped from the copied helper  [F13]", ("a.Injective ∧\n  (1 ≤ a) ∧", "a.Injective ∧\n ")),
            ("wrong category in header", ("fc-category: research open", "fc-category: research solved")),
            ("answer( in a comment", ("\nend Erdos261", "\n-- answer(sorry)\nend Erdos261")),
        ]
        for i, (name, (old, new)) in enumerate(mutations):
            if old not in good:
                raise CheckError(f"self-test fixture is stale: {old[:40]!r} not in the rendering")
            expect(name, False, lambda i=i, old=old, new=new:
                   run_check(fixture(f"m{i}.lean", good.replace(old, new, 1)), lean=False),
                   why="differs from the rendering")
        expect("wrong SHA", False,
               lambda: run_check(fixture("sha.lean", good.replace(fc_resolve(fc, SHA_HEAD), "0" * 40)), lean=False),
               why="git")
        expect("theorem that does not exist", False,
               lambda: run_check(fixture("thm.lean", good.replace("fc-theorem: erdos_261.parts.ii",
                                                                  "fc-theorem: erdos_261.parts.iv")), lean=False),
               why="not found")

        def extract_389():
            _, st, _ = extract(fc_show(fc, SHA_HEAD, "FormalConjectures/ErdosProblems/389.lean"), "erdos_389")
            shape, f = normalize(st)
            want = "∀ n ≥ 1, ∃ k ≥ 1, ∏ i ∈ Finset.range k, (n + i) ∣ ∏ i ∈ Finset.range k, (n + k + i)"
            return [] if (shape, f["body"]) == ("iff", want) else [f"got {shape} {f['body']!r}"]
        expect("extraction stops before a trailing ':= by' (389)", True, extract_389)

        def render_1063():
            full, _, _ = render(fc, SHA_HEAD, "FormalConjectures/ErdosProblems/1063.lean",
                                "erdos_1063.better_upper")
            ok = ("def Statement (upper_bound : ℕ → ℝ) : Prop :=\n    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧"
                  in full and "(((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)\n" in full and "answer(" not in full)
            return [] if ok else ["unexpected rendering of 1063"]
        expect("let-shape rendering handles ':=' inside the statement (1063)", True, render_1063)

        old = render(fc, SHA_261_OLD, P261, "erdos_261.variants.two_representations")[0]
        p_old = fixture("tworeps.lean", old)
        expect("pinned check of two_representations at its old SHA", True, lambda: run_check(p_old, lean=False))
        expect("drift: two_representations changed upstream (open -> solved)", False,
               lambda: run_drift(p_old, SHA_261_NEW, fc)[0], why="cannot render")
        p_ii = fixture("ii_old.lean", render(fc, SHA_261_NEW, P261, "erdos_261.parts.ii")[0])
        expect("drift: parts.ii unchanged between two later SHAs", True, lambda: run_drift(p_ii, SHA_HEAD, fc)[0])

        # Drift when only a copied definition changes: a scratch FC clone with one extra commit.
        fake = os.path.join(d, "fake")
        subprocess.run(["git", "clone", "-q", "--no-hardlinks", fc, fake], check=True)
        git(fake, "checkout", "-q", SHA_HEAD)
        src = os.path.join(fake, P261)
        orig = open(src, encoding="utf-8").read()       # read before opening for write
        if "(t ≥ 2)" not in orig:
            raise CheckError("self-test fixture is stale: (t ≥ 2) not in 261.lean")
        open(src, "w", encoding="utf-8").write(orig.replace("(t ≥ 2)", "(t ≥ 3)", 1))
        git(fake, "-c", "user.name=selftest", "-c", "user.email=selftest@invalid", "commit", "-q", "-am", "def change")
        p_fake = fixture("fake.lean", render(fake, SHA_HEAD, P261, "erdos_261.parts.ii")[0])
        expect("drift: only a copied definition changes upstream", False,
               lambda: run_drift(p_fake, "HEAD", fake)[0], why="copied text changed upstream")

        if lean:
            work = os.path.join(REPO, ".lake", "fc_statement")
            os.makedirs(work, exist_ok=True)
            pinned = fc_resolve(fc, SHA_HEAD)
            gp = os.path.join(work, "selftest_good.lean")
            open(gp, "w", encoding="utf-8").write(good)
            expect("Lean step on the rendered file", True, lambda: lean_step(gp, decl, fc, pinned))
            bp = os.path.join(work, "selftest_bad.lean")
            open(bp, "w", encoding="utf-8").write(good.replace("Erdos261Prop n\n", "Erdos261Prop' n\n"))
            expect("Lean step compiles the file itself (broken file fails)  [F10]", False,
                   lambda: lean_step(bp, decl, fc, pinned), why="does not compile")
            sp = os.path.join(work, "selftest_sorry.lean")
            open(sp, "w", encoding="utf-8").write(
                good.replace("def Statement : Prop :=\n", "def Statement : Prop := sorry\ndef Unused : Prop :=\n"))
            expect("Lean step rejects a sorry-backed statement", False,
                   lambda: lean_step(sp, decl, fc, pinned), why="non-standard axioms")
            # Collision guard: FC's helper library (in the scratch clone) defines a constant
            # that the statement uses; the Mathlib-only file resolves it elsewhere.
            helper = os.path.join(fake, "FormalConjecturesForMathlib", "SelfTestClash.lean")
            os.makedirs(os.path.dirname(helper), exist_ok=True)
            open(helper, "w", encoding="utf-8").write(
                "namespace Function\n\ndef Injective (f : Nat → Nat) : Prop := True\n\nend Function\n")
            git(fake, "add", "-A")
            git(fake, "-c", "user.name=selftest", "-c", "user.email=selftest@invalid", "commit", "-q", "-m", "clash")
            expect("Lean step flags a constant FC defines in its helper library", False,
                   lambda: lean_step(gp, decl, fake, fc_resolve(fake, "HEAD")), why="Function.Injective")

    n_ok = sum(results)
    print(f"self-test: {n_ok}/{len(results)} behaved as expected (for the expected reason)")
    return 0 if n_ok == len(results) else 1


# ---------------------------------------------------------------- CLI

def main(argv):
    if not os.path.isdir(os.path.join(FC_DEFAULT, ".git")):
        print(f"no FC clone at {FC_DEFAULT}: git clone "
              f"https://github.com/google-deepmind/formal-conjectures.git .cache/formal-conjectures", file=sys.stderr)
        return 2
    if argv[:1] == ["--self-test"]:
        return self_test(lean="--no-lean" not in argv)
    if len(argv) >= 3 and argv[0] == "render":
        sha = argv[argv.index("--sha") + 1] if "--sha" in argv else "HEAD"
        sys.stdout.write(render(FC_DEFAULT, sha, argv[1], argv[2])[0])
        return 0
    if len(argv) >= 2 and argv[0] == "check":
        problems = run_check(argv[1], lean="--no-lean" not in argv)
        for p in problems:
            print("  FAIL ", p)
        print("pinned check:", "FAIL" if problems else "ok")
        return 1 if problems else 0
    if len(argv) >= 2 and argv[0] == "drift":
        if "--fetch" in argv:
            git(FC_DEFAULT, "fetch", "-q", "origin")
        ref = argv[argv.index("--ref") + 1] if "--ref" in argv else "origin/main"
        problems, at = run_drift(argv[1], ref)
        for p in problems:
            print("  DRIFT", p)
        print(f"drift check against {ref} ({at[:8]}):", "DRIFT" if problems else "no drift")
        return 1 if problems else 0
    print(__doc__, file=sys.stderr)
    return 2


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv[1:]))
    except CheckError as e:
        print("  FAIL ", e)
        sys.exit(1)
