#!/usr/bin/env python3
"""Forbidden-construct scan of the library's proof files.

    scripts/lean_forbidden.py FILE...

Run from lean/, for example on every proof module:

    python3 scripts/lean_forbidden.py $(find RebuildBound/Proofs -name '*.lean')

Prints one line per hit, `file:line: <construct>: <source line>`, and exits 1
if there is any hit, 2 if a file cannot be scanned.

Comments are removed first: line comments `--`, block comments `/- -/`
(nested, including doc comments `/-- -/` and `/-! -/`). The lexer knows
string literals (with escapes), raw strings `r#"..."#`, character literals
and `«»` identifiers, so a `--` inside one of them does not start a comment.
String and character literals are kept: a forbidden word inside a string is
reported too. The scan fails closed: an unterminated comment, string or
`«` is an error.

What is forbidden, and why:
  - proof holes and axioms: sorry, admit, sorryAx, axiom;
  - code the kernel does not check: unsafe, implemented_by, extern,
    native_decide, `native` (as in `decide +native`), ofReduceBool, any
    `debug.` option (e.g. debug.skipKernelTC, debug.byAsSorry);
  - metaprogramming, which can rewrite the environment the audits read: run_cmd, run_elab, run_meta, run_tac,
    by_elab, #eval, elab, elab_rules, macro, macro_rules, syntax,
    initialize, builtin_initialize, simproc, dsimproc, meta, modifyEnv,
    setEnv, `open private`, and any name rooted at `Lean` (which covers
    `import Lean`, `open Lean` and `Lean.Elab...`);
  - imports other than Init, Std, Mathlib and RebuildBound modules;
  - attributes outside ALLOWED_ATTRIBUTES (elaborator-registering
    attributes such as `@[tactic ...]` or `@[command_elab ...]` would run
    package code at elaboration time).
"""

import re
import sys

WORDS = [
    "sorry", "admit", "sorryAx", "axiom",
    "unsafe", "implemented_by", "extern", "native_decide",
    "ofReduceBool", "skipKernelTC",
    "run_cmd", "run_elab", "run_meta", "run_tac", "by_elab",
    "elab", "elab_rules", "macro", "macro_rules", "syntax",
    "initialize", "builtin_initialize", "simproc", "dsimproc", "meta",
    "modifyEnv", "setEnv", "Lean",
]
# Identifier characters: Python's \w (Unicode letters, digits, subscripts, _)
# plus Lean's ' ! ?.
ID = r"[\w'!?]"
FORBIDDEN = re.compile(
    rf"(?<!{ID})(?:{'|'.join(WORDS)})(?!{ID})"  # whole identifiers
    rf"|#eval(?!{ID})"
    rf"|(?<!{ID})debug\s*\."                    # set_option debug.*
    rf"|\+\s*native(?!{ID})|(?<!{ID})native\s*:="  # decide +native
    rf"|(?<!{ID})open\s+private(?!{ID})")
IMPORT = re.compile(rf"(?<!{ID})import\s+(?:all\s+)?([^\s]+)")
IMPORT_OK = re.compile(r"(Init|Std|Mathlib|RebuildBound)(\.[\w'.]+)?$")
ATTRIBUTE = re.compile(rf"(@\[|(?<!{ID})attribute\s*\[)")
ALLOWED_ATTRIBUTES = {
    "simp", "ext", "reducible", "irreducible", "semireducible", "instance",
    "simps", "gcongr", "norm_cast", "push_cast", "fun_prop", "measurability",
    "mono", "congr", "elab_as_elim", "nolint", "deprecated", "inline",
    "specialize", "symm", "trans", "refl", "nontriviality", "bound",
    "field_simps", "induction_eliminator", "cases_eliminator",
    "match_pattern", "inherit_doc", "coe",
}


class ScanError(Exception):
    pass


def is_ident_char(c):
    return c.isalnum() or c in "_'!?"


CHAR_LIT = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|[\\\"'ntr])|[^\\'\n])'")
RAW_START = re.compile(r'r(#*)"')


def strip_comments(src):
    """Return src with every comment character replaced by a space (newlines
    are kept, so line numbers do not move)."""
    out = []
    i, n = 0, len(src)

    def blank(s):
        return "".join(c if c == "\n" else " " for c in s)

    while i < n:
        c = src[i]
        prev = src[i - 1] if i > 0 else "\n"
        if src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            out.append(blank(src[i:j]))
            i = j
        elif src.startswith("/-", i):
            depth, j = 1, i + 2
            while depth > 0:
                if j >= n:
                    raise ScanError(f"unterminated block comment at offset {i}")
                if src.startswith("/-", j):
                    depth, j = depth + 1, j + 2
                elif src.startswith("-/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append(blank(src[i:j]))
            i = j
        elif c == '"':
            j = i + 1
            while True:
                if j >= n:
                    raise ScanError(f"unterminated string at offset {i}")
                if src[j] == "\\":
                    j += 2
                elif src[j] == '"':
                    j += 1
                    break
                else:
                    j += 1
            out.append(src[i:j])
            i = j
        elif c == "r" and not is_ident_char(prev) and RAW_START.match(src, i):
            m = RAW_START.match(src, i)
            end = '"' + m.group(1)
            j = src.find(end, m.end())
            if j < 0:
                raise ScanError(f"unterminated raw string at offset {i}")
            j += len(end)
            out.append(src[i:j])
            i = j
        elif c == "'" and not is_ident_char(prev) and CHAR_LIT.match(src, i):
            j = CHAR_LIT.match(src, i).end()
            out.append(src[i:j])
            i = j
        elif c == "«":
            j = src.find("»", i)
            if j < 0:
                raise ScanError(f"unterminated « at offset {i}")
            out.append(src[i:j + 1])
            i = j + 1
        else:
            # Copy a run of ordinary characters at once.
            j = i + 1
            while j < n and src[j] not in "-/\"r'«":
                j += 1
            out.append(src[i:j])
            i = j
    return "".join(out)


def split_top_level(s):
    parts, depth, cur = [], 0, ""
    for c in s:
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth -= 1
        if c == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += c
    parts.append(cur)
    return parts


def attribute_hits(code):
    """(offset, message) for every attribute outside ALLOWED_ATTRIBUTES."""
    hits = []
    for m in ATTRIBUTE.finditer(code):
        depth, j = 1, m.end()
        while j < len(code) and depth > 0:
            depth += {"[": 1, "]": -1}.get(code[j], 0)
            j += 1
        body = code[m.end():j - 1]
        for entry in split_top_level(body):
            words = entry.replace("-", " ").split()
            while words and words[0] in ("local", "scoped"):
                words = words[1:]
            name = words[0] if words else ""
            if name not in ALLOWED_ATTRIBUTES:
                hits.append((m.start(), f"attribute `{name}` (not in the allowlist)"))
    return hits


def scan(path):
    with open(path, encoding="utf-8") as f:
        src = f.read()
    code = strip_comments(src)
    hits = [(m.start(), " ".join(m.group().split())) for m in FORBIDDEN.finditer(code)]
    for m in IMPORT.finditer(code):
        if not IMPORT_OK.match(m.group(1)):
            hits.append((m.start(), f"import of {m.group(1)}"))
    hits += attribute_hits(code)
    lines = src.split("\n")
    result = []
    for off, name in sorted(hits):
        ln = code.count("\n", 0, off)
        result.append(f"{path}:{ln + 1}: {name}: {lines[ln].strip()}")
    return result


def main(argv):
    if len(argv) < 2:
        print(__doc__.strip().split("\n\n")[1], file=sys.stderr)
        return 2
    status = 0
    for path in argv[1:]:
        try:
            hits = scan(path)
        except (OSError, UnicodeDecodeError, ScanError) as e:
            print(f"{path}: cannot scan: {e}")
            status = 2
            continue
        for h in hits:
            print(h)
        if hits and status == 0:
            status = 1
    return status


if __name__ == "__main__":
    sys.exit(main(sys.argv))
