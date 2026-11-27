#!/usr/bin/env python3
"""Proof-hygiene guard (Plan.md section 3 rule 1, section 4 S1/S4; task 0.3).

Standard library only; run with `python3 -I`.  Adapted from safe-pdf's scripts/hygiene.py.

  hygiene.py [scan] [--root DIR]   scan Lean sources for forbidden constructs (comments and
                                   string literals ignored) and check that every non-private
                                   `theorem` in JPEG2000/ and Spec/ is listed in
                                   scripts/axioms.lean
  hygiene.py axioms [--root DIR]   read `lake env lean scripts/axioms.lean` output on stdin;
                                   fail on any axiom other than propext, Classical.choice,
                                   Quot.sound, or if a `#print axioms` line produced no result
  hygiene.py --self-test           run the built-in tests of this script

Strict trees (JPEG2000/, Spec/, Encode/ and their umbrella files) forbid: IO (IO, EIO, BaseIO),
partial, unsafe (and unsafe*/…Unsafe identifiers), panic!, any `ident!` call (get!, head!,
getElem!, …), `xs[i]!` indexing, implemented_by, extern, Float, dbg_trace/dbgTrace, axiom,
native_decide / `decide +native`, sorry/admit.
Every other .lean file under the root (Tests/, Bench/, Fuzz/, scripts/, …; hidden dirs such
as .lake/ and .git/ skipped) forbids sorry/admit.
Output: one `path:line: message` per violation; exit status 1 if any.
"""
import os
import re
import sys

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
STRICT_DIRS = ("JPEG2000", "Spec", "Encode")
STRICT_FILES = ("JPEG2000.lean", "Spec.lean", "Encode.lean")
# Trees whose theorems must all appear in scripts/axioms.lean (task 0.3).
LISTED_DIRS = ("JPEG2000", "Spec")
AXIOMS_FILE = os.path.join("scripts", "axioms.lean")

# `name!` forms that are not partial calls: string-interpolation macros (s!, m!, f!), the
# version literal v!, and tactic variants (simp!, simp_all!, dsimp!, simp_arith!, decide!).
BANG_OK = r"(?:[smfv]|simp|simp_all|dsimp|simp_arith|simpa|decide)!"

SORRY = ("sorry/admit", re.compile(r"\b(?:sorry|sorryAx|admit)\b"))
STRICT_RULES = [
    ("IO", re.compile(r"\b(?:E|Base)?IO\b")),
    ("partial", re.compile(r"\bpartial\b")),
    ("unsafe", re.compile(r"\bunsafe\w*|\b\w+Unsafe\w*")),
    ("panic!", re.compile(r"\bpanic!")),
    ("`!` call (get!/head!/...)",
     re.compile(r"(?<![\w'.!])(?!" + BANG_OK + r"(?!\w))[\w.']*[A-Za-z_][\w']*!(?!=)")),
    ("`[i]!` indexing", re.compile(r"[\]\)]!(?!=)")),
    ("implemented_by", re.compile(r"\bimplemented_by\b")),
    ("extern", re.compile(r"\bextern\b")),
    ("Float (Plan.md section 3 rule 4)",
     re.compile(r"\b(?:Float|Float32|FloatArray|Float32Array|toFloat|toFloat32|ofFloat)\b")),
    ("dbg_trace/dbgTrace", re.compile(r"\bdbg_trace\w*|\bdbgTrace\w*")),
    ("axiom declaration", re.compile(r"\baxiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b|\+\s*native\b")),
    SORRY,
]
ANY_RULES = [SORRY]


def _blank(ch):
    return "\n" if ch == "\n" else " "


def _ident_char(ch):
    return ch.isalnum() or ch in "_'!?"


def strip_code(src):
    """Replace comments and string/char literals by spaces, preserving line structure.

    The `{…}` holes of interpolated strings (`s!"…"`, `m!"…"`, `f!"…"`) are kept as code.
    """
    out = []
    i, n = 0, len(src)
    while i < n:
        c = src[i]
        two = src[i:i + 2]
        if two == "--":
            while i < n and src[i] != "\n":
                out.append(" ")
                i += 1
        elif two == "/-":
            depth = 0
            while i < n:
                if src[i:i + 2] == "/-":
                    depth += 1
                    out.append("  ")
                    i += 2
                elif src[i:i + 2] == "-/":
                    depth -= 1
                    out.append("  ")
                    i += 2
                    if depth == 0:
                        break
                else:
                    out.append(_blank(src[i]))
                    i += 1
        elif c == "r" and (i == 0 or not _ident_char(src[i - 1])) and re.match(r'r#*"', src[i:]):
            m = re.match(r'r(#*)"', src[i:])
            close = '"' + m.group(1)
            j = src.find(close, i + m.end())
            j = n if j < 0 else j + len(close)
            out.extend(_blank(ch) for ch in src[i:j])
            i = j
        elif c == '"':
            interp = i > 0 and src[i - 1] == "!"
            out.append(" ")
            j = i + 1
            while j < n and src[j] != '"':
                if src[j] == "\\" and j + 1 < n:
                    out.append(_blank(src[j]) + _blank(src[j + 1]))
                    j += 2
                elif interp and src[j] == "{":
                    # keep the hole as code (one level of brace nesting tracked)
                    depth = 0
                    while j < n:
                        if src[j] == "{":
                            depth += 1
                        elif src[j] == "}":
                            depth -= 1
                        out.append(src[j])
                        j += 1
                        if depth == 0:
                            break
                else:
                    out.append(_blank(src[j]))
                    j += 1
            if j < n:
                out.append(" ")
                j += 1
            i = j
        elif c == "'" and (i == 0 or not _ident_char(src[i - 1])):
            m = re.match(r"'(\\(x[0-9a-fA-F]{2}|u\{[0-9a-fA-F]+\}|.)|[^\\'\n])'", src[i:])
            if m:
                out.append(" " * m.end())
                i += m.end()
            else:
                out.append(c)
                i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def lean_files(path):
    if os.path.isfile(path):
        return [path] if path.endswith(".lean") else []
    found = []
    for d, dirs, files in os.walk(path):
        dirs[:] = sorted(x for x in dirs if not x.startswith("."))
        found += [os.path.join(d, f) for f in sorted(files) if f.endswith(".lean")]
    return found


def check_source(code, strict):
    """Return [(line, message)] for already-stripped code."""
    rules = STRICT_RULES if strict else ANY_RULES
    hits = []
    for ln, line in enumerate(code.split("\n"), 1):
        for name, rx in rules:
            if rx.search(line):
                hits.append((ln, "forbidden " + name))
    return hits


_NS_RE = re.compile(r"^\s*(namespace|section|end|mutual)\b\s*([^\s]*)")
_THM_RE = re.compile(r"(?<![\w.'])theorem\s+([^\s:({\[⦃]+)")


def theorems(code):
    """Yield (line, full name) for every non-private `theorem` in stripped code."""
    stack = []  # entries: ("ns", [parts]) | ("sec", None) | ("mutual", None)
    for ln, line in enumerate(code.split("\n"), 1):
        m = _NS_RE.match(line)
        if m:
            kind, arg = m.group(1), m.group(2)
            if kind == "namespace" and arg:
                stack.append(("ns", arg.split(".")))
            elif kind in ("section", "mutual"):
                stack.append((kind, None))
            elif kind == "end" and stack:
                stack.pop()
            continue
        t = _THM_RE.search(line)
        if not t or re.search(r"\bprivate\b", line[:t.start()]):
            continue
        name = t.group(1)
        if name.startswith("_root_."):
            full = name[len("_root_."):]
        else:
            prefix = [p for k, parts in stack if k == "ns" for p in parts]
            full = ".".join(prefix + [name])
        yield ln, full


def listed_theorems(axioms_code):
    return set(re.findall(r"#print\s+axioms\s+([^\s]+)", axioms_code))


def scan(root):
    strict = set()
    for t in STRICT_DIRS + STRICT_FILES:
        p = os.path.join(root, t)
        if os.path.exists(p):
            strict.update(lean_files(p))
    listed_scope = set()
    for t in LISTED_DIRS:
        p = os.path.join(root, t)
        if os.path.exists(p):
            listed_scope.update(lean_files(p))
    allfiles = set(lean_files(root)) | strict

    ax_path = os.path.join(root, AXIOMS_FILE)
    listed = None
    if os.path.isfile(ax_path):
        with open(ax_path, encoding="utf-8", errors="replace") as fh:
            listed = listed_theorems(strip_code(fh.read()))

    violations = []
    if listed is None:
        violations.append("%s:1: missing (needed for the axioms check)" % AXIOMS_FILE)
    for f in sorted(allfiles):
        rel = os.path.relpath(f, root)
        with open(f, encoding="utf-8", errors="replace") as fh:
            code = strip_code(fh.read())
        for ln, msg in check_source(code, f in strict):
            violations.append("%s:%d: %s" % (rel, ln, msg))
        if f in listed_scope and listed is not None:
            for ln, name in theorems(code):
                if name not in listed:
                    violations.append("%s:%d: theorem %s is not listed in %s"
                                      % (rel, ln, name, AXIOMS_FILE))
    return violations


_AX_RE = re.compile(
    r"(?m)^'(.+?)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])")


def check_axioms(text):
    """Parse `#print axioms` output. Return (names seen, [problems])."""
    seen, bad = [], []
    for m in _AX_RE.finditer(text):
        seen.append(m.group(1))
        if m.group(3) is not None:
            axs = [a.strip() for a in m.group(3).replace("\n", " ").split(",") if a.strip()]
            extra = [a for a in axs if a not in ALLOWED_AXIOMS]
            if extra:
                bad.append("%s depends on disallowed axiom(s): %s"
                           % (m.group(1), ", ".join(extra)))
    return seen, bad


def axioms_main(root, text):
    ax_path = os.path.join(root, AXIOMS_FILE)
    with open(ax_path, encoding="utf-8", errors="replace") as fh:
        expected = listed_theorems(strip_code(fh.read()))
    seen, bad = check_axioms(text)
    for b in bad:
        print("%s: %s" % (AXIOMS_FILE, b))
    missing = sorted(expected - set(seen))
    for name in missing:
        print("%s: no `#print axioms` result for %s" % (AXIOMS_FILE, name))
    if not seen:
        print("%s: no `#print axioms` results found in Lean output" % AXIOMS_FILE)
    if bad or missing or not seen:
        return 1
    print("hygiene: axioms OK (%d theorems checked)" % len(seen))
    return 0


# ---------------------------------------------------------------------------------------------
# Self-test

_STRICT_BAD = [
    "def f : IO Unit := pure ()",
    "def f (x : Nat) : EIO String Nat := pure x",
    "def g : BaseIO Unit := pure ()",
    "  IO.println \"hi\"",
    "partial def loop : Nat → Nat := loop",
    "unsafe def u : Nat := 0",
    "def c := unsafeCast (0 : Nat)",
    "def p := ptrAddrUnsafe 0",
    "def h : Nat := panic! \"boom\"",
    "def a (xs : Array Nat) := xs.get! 0",
    "def a (xs : List Nat) := xs.head!",
    "def a (xs : Array Nat) := xs[0]!",
    "def a (xs : Array Nat) (i : Nat) := (xs.map id)[i]! + 1",
    "def a (xs : Array Nat) := getElem! xs 0",
    "def a (xs : Array Nat) := xs.back!.succ",
    "def a := xs[i]! == 3",
    "@[implemented_by fastF] def f := 0",
    "@[extern \"c_f\"] opaque f : Nat → Nat",
    "def x : Float := 1.5",
    "def y (n : Nat) := n.toFloat",
    "def z := Float32.ofNat 3",
    "def d (n : Nat) := dbg_trace \"x\"; n",
    "def d (n : Nat) := dbgTrace \"x\" fun _ => n",
    "axiom cheat : False",
    "theorem t : 2 + 2 = 4 := by native_decide",
    "theorem t : 2 + 2 = 4 := by decide +native",
    "theorem t : False := sorry",
    "theorem t : False := by admit",
    "def m := s!\"{xs[0]!}\"",
]

_STRICT_OK = [
    "def ne (a b : Nat) : Bool := a != b",
    "def nb (b : Bool) : Bool := !b",
    "def nb2 (b : Bool) : Bool := (!b) && b",
    "def ne2 (xs : Array Nat) := xs[0]? != some 1",
    "def ne3 (xs : Array Nat) (h : 0 < xs.size) := xs[0]'h != 1",
    "def gd (xs : Array Nat) := xs.getD 0 0",
    "def s (n : Nat) : String := s!\"n = {n}\"",
    "def s (n : Nat) : String := s!\"n = {n + 1}!\"",
    "-- partial def in a comment; IO; sorry; xs[i]!; Float",
    "/-- This is partially specified; uses `IO`, `xs[i]!`, `get!`, sorry, unsafe, Float. -/",
    "/- nested /- block -/ still partial sorry -/ def ok := 1",
    "def str := \"partial unsafe sorry IO panic! get! xs[0]! Float -- \"",
    "def str := r#\"sorry \"quoted\" IO\"#",
    "def ch := '!'",
    "def ch := '\"'",
    "def x' := 1",
    "theorem t (b : Bool) : (!!b) = b := by cases b <;> rfl",
    "theorem t (n : Nat) : n + 0 = n := by simp!",
    "theorem t (n : Nat) : n + 0 = n := by simp_all!",
    "def partialSum (xs : List Nat) := xs.foldl (· + ·) 0",
    "def IOError := Nat",
    "def floatingPoint := 0",
    "def isPartial := true",
    "structure Ratio where num : Int",
    "def sorryless := 0",
    "def externalLimit := 0",
    "def x := 1 -- trailing comment with get! and IO",
]

_ANY_BAD = [
    "theorem t : False := sorry",
    "example : False := by admit",
    "def x := s!\"{(sorry : Nat)}\"",
]
_ANY_OK = [
    "def main : IO Unit := IO.println \"sorry\"",
    "partial def loop (n : Nat) : IO Unit := loop n",
    "def a (xs : Array Nat) := xs[0]!",
    "-- sorry",
    "/-- not a sorry -/ def x := 1",
]

_THM_SRC = """
namespace JPEG2000
theorem top : True := trivial
namespace MQ
/-- doc with theorem fake : in a comment -/
@[simp] theorem roundtrip (n : Nat) : n = n := rfl
private theorem hidden : True := trivial
protected theorem prot : True := trivial
theorem _root_.rootThm : True := trivial
section Foo
theorem inSection : True := trivial
end Foo
end MQ
theorem after : True := trivial
mutual
theorem m1 : True := trivial
end
end JPEG2000
theorem bare : True := trivial
"""
_THM_EXPECT = ["JPEG2000.top", "JPEG2000.MQ.roundtrip", "JPEG2000.MQ.prot", "rootThm",
               "JPEG2000.MQ.inSection", "JPEG2000.after", "JPEG2000.m1", "bare"]

_AX_OUT_OK = """'A.t1' depends on axioms: [propext, Classical.choice, Quot.sound]
'A.t2' does not depend on any axioms
'A.t3'' depends on axioms: [propext,
 Quot.sound]
"""
_AX_OUT_BAD = [
    "'A.t' depends on axioms: [sorryAx]",
    "'A.t' depends on axioms: [propext, Lean.ofReduceBool]",
    "'A.t' depends on axioms: [Lean.trustCompiler, Quot.sound]",
    "'A.t' depends on axioms: [A.t._native.native_decide.ax_1_1]",
    "'A.t' depends on axioms: [propext,\n  myAxiom]",
]


def self_test():
    import tempfile
    fails = []

    def expect(cond, what):
        if not cond:
            fails.append(what)

    for s in _STRICT_BAD:
        expect(check_source(strip_code(s), True), "strict should reject: " + s)
    for s in _STRICT_OK:
        hits = check_source(strip_code(s), True)
        expect(not hits, "strict should accept: %s  (got %s)" % (s, hits))
    for s in _ANY_BAD:
        expect(check_source(strip_code(s), False), "any should reject: " + s)
    for s in _ANY_OK:
        hits = check_source(strip_code(s), False)
        expect(not hits, "any should accept: %s  (got %s)" % (s, hits))

    # line numbers survive stripping
    src = "/- a\nb -/\ndef s := \"x\ny\"\ndef a := xs[0]!\n"
    expect([ln for ln, _ in check_source(strip_code(src), True)] == [5], "line numbering")

    got = [n for _, n in theorems(strip_code(_THM_SRC))]
    expect(got == _THM_EXPECT, "theorem names: got %s" % got)

    seen, bad = check_axioms(_AX_OUT_OK)
    expect(seen == ["A.t1", "A.t2", "A.t3'"] and not bad, "axioms ok: %s %s" % (seen, bad))
    for out in _AX_OUT_BAD:
        _, bad = check_axioms(out)
        expect(bad, "axioms should reject: " + out)

    # whole-tree scan on a synthetic repository
    with tempfile.TemporaryDirectory() as root:
        def put(rel, text):
            p = os.path.join(root, rel)
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w", encoding="utf-8") as fh:
                fh.write(text)

        put("scripts/axioms.lean", "import JPEG2000\n#print axioms JPEG2000.listed\n"
                                   "-- #print axioms JPEG2000.commented\n")
        put("JPEG2000/A.lean", "namespace JPEG2000\ntheorem listed : True := trivial\n"
                               "theorem commented : True := trivial\nend JPEG2000\n")
        put("Spec/B.lean", "def f (xs : Array Nat) := xs[0]!\n")
        put("Tests/C.lean", "def main : IO Unit := pure ()\ntheorem t : False := sorry\n")
        put("Encode/D.lean", "theorem e : True := trivial\n")  # Encode: not required listed
        put(".lake/E.lean", "theorem t : False := sorry\n")  # hidden: skipped
        v = scan(root)
        want = ["JPEG2000/A.lean:3: theorem JPEG2000.commented is not listed in "
                "scripts/axioms.lean",
                "Spec/B.lean:1: forbidden `[i]!` indexing",
                "Tests/C.lean:2: forbidden sorry/admit"]
        expect(v == want, "scan: got %s" % v)
        put("JPEG2000/A.lean", "namespace JPEG2000\ntheorem listed : True := trivial\n"
                               "end JPEG2000\n")
        put("Spec/B.lean", "def f (xs : Array Nat) := xs[0]?\n")
        put("Tests/C.lean", "def main : IO Unit := pure ()\n")
        expect(scan(root) == [], "clean scan: got %s" % scan(root))
        os.remove(os.path.join(root, AXIOMS_FILE))
        expect(scan(root) != [], "missing axioms.lean must fail")

    for f in fails:
        print("self-test FAIL: " + f)
    if fails:
        print("hygiene self-test: %d failure(s)" % len(fails), file=sys.stderr)
        return 1
    print("hygiene self-test: OK")
    return 0


def main(argv):
    args = argv[1:]
    if args == ["--self-test"]:
        return self_test()
    root = "."
    if "--root" in args:
        k = args.index("--root")
        if k + 1 >= len(args):
            print(__doc__, file=sys.stderr)
            return 2
        root = args[k + 1]
        del args[k:k + 2]
    cmd = args[0] if args else "scan"
    if args[1:] or cmd not in ("scan", "axioms"):
        print(__doc__, file=sys.stderr)
        return 2
    if cmd == "axioms":
        return axioms_main(root, sys.stdin.read())
    v = scan(root)
    for line in v:
        print(line)
    if v:
        print("hygiene: %d violation(s)" % len(v), file=sys.stderr)
        return 1
    print("hygiene: source scan OK")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
