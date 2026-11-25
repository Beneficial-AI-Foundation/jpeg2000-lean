# jpeg2000-lean — instructions for Claude

A formally verified, fast JPEG 2000 decoder in Lean 4. The design document is
[Plan.md](Plan.md); progress, tasks, gotchas and decisions live in [progress.md](progress.md)
(the ledger, maintained by `/next-wave`).

## Commands

| What | Command |
|---|---|
| Build (libraries `JPEG2000`, `Spec`, `Encode`) | `lake build` |
| Build the test executable | `lake build tests` |
| Tests | `lake exe tests` |
| Guard: proof hygiene | `scripts/check-hygiene.sh` (once task 0.3 lands) |
| Corpus fetch / verify | `python3 -I scripts/fetch-corpus.py` / `--check` (once task 0.5 lands) |
| Single-file check | `lake env lean <path/to/File.lean>` |

The gate for every commit is: `lake build && lake build tests && lake exe tests`, plus every
guard listed above that exists.

The single-file check compiles one file against the **already built** `.olean`s of its
imports. It does not write to `.lake/`, so it is safe to run in the shared checkout while
nothing else builds. It can only import modules that are already built in the main
checkout; a new file importing another new, unbuilt file must say so in its report instead.

## Concurrent builds

**Concurrent builds in one checkout are NOT safe.** Only the orchestrator runs `lake build`,
`lake exe …` or any executable in the main checkout. A subagent in the shared checkout uses
only the single-file check. A subagent in its own git worktree may build and test freely
there; the project has no Lake dependencies, so a fresh worktree builds from scratch quickly
and needs no cache sharing.

## Lean MCP server (`lean-lsp`, configured in `.mcp.json`)

It runs `lake serve` in the main checkout (`lean_build` is disabled). Use its read-only tools
(`lean_goal`, `lean_diagnostic_messages`, `lean_hover_info`, `lean_multi_attempt`,
`lean_run_code`, `lean_local_search`) only while no `lake build` runs in the main checkout.
In a worktree the server's project path still points at the main checkout, so worktree
subagents build and check with `lake` locally and use the MCP only for search and scratch
snippets.

**Every agent working on Lean code uses the Lean MCP tools as its primary proof loop** (load
them with ToolSearch `lean_` when they are deferred):

* **Shared checkout (`new` tasks):** develop proofs with `lean_goal`,
  `lean_diagnostic_messages`, `lean_multi_attempt` and `lean_hover_info` instead of repeated
  whole-file runs. Run `lake env lean <file>` once at the end and quote it in the report.
* **Worktree (`wt` tasks):** build and check with `lake` locally; still use the MCP search
  tools and `lean_run_code`.
* **Finding lemmas:** search before proving a helper (`lean_local_search`; `exact?` via
  `lean_multi_attempt`). There is no Mathlib and no Batteries: a lemma that lives only there
  is not usable. In the sandbox, loogle/leansearch are blocked.
* If the `lean_*` tools are missing in a session, say so in the report and fall back to
  `lake env lean`; do not stop.

## Shared registries (subagents never edit these; report the lines to add)

* `JPEG2000.lean`, `Spec.lean`, `Encode.lean` — umbrella imports of every module under
  `JPEG2000/`, `Spec/`, `Encode/`.
* `Tests/Main.lean` — the `suites` list and its imports. Every module under `Tests/` belongs
  to lib `Tests` by glob, so new test modules need no lakefile line.
* `lakefile.lean` — targets and options.
* `scripts/axioms.lean` — the theorems whose axioms the guard checks (once 0.3 lands).
* `progress.md` — the ledger (orchestrator only).

## Layout (Plan.md §12)

* `JPEG2000/` — the decoder: pure and total. **No `IO`, no `partial`, no `unsafe`, no
  `panic!`, no `!` indexing (`get!`, `xs[i]!`), no `sorry`** (Plan.md §3 rule 1).
* `Spec/` — executable specifications and theorems; same rules as `JPEG2000/`.
* `Encode/` — reference encoder (tests and proofs only); same rules.
* `Tests/`, `Bench/`, `Fuzz/` — `IO` allowed, still no `sorry`.
* `scripts/` — guards, corpus fetch, differential and benchmark scripts.
* `corpus/manifest.json` is committed; downloaded files go to `corpus/files/` (git-ignored).
* `docs/` — proof patterns, deviations from the standard, corpus notes, performance log.

## Conventions

* Toolchain `leanprover/lean4:v4.36.0`, **no Lake dependencies** (no Mathlib, no Batteries);
  changing either needs a ledger Decisions entry. `autoImplicit = false`.
* **No floating point** anywhere in the decoder; 9/7 and ICT are fixed point (Plan.md §5.4).
* Every loop is structurally recursive or carries a measure/fuel justified by the input size
  or a `Limits` field (Plan.md §3 rule 2). Never `partial def`.
* Every size the stream declares is checked against `JPEG2000.Limits` before anything is
  allocated; excess returns `Error.limitExceeded` (Plan.md §3 rule 3). Errors are values of
  `JPEG2000.Error`.
* Spec first: for each stage write the spec in `Spec/`, the implementation in `JPEG2000/`,
  then the equivalence theorem (Plan.md §5.1). Theorem IDs (S1–S6, C1–C10) follow Plan.md §4.
* Hot code uses `UInt32`/`UInt64`/`Int32`/`Int64` and `ByteArray`-backed buffers; compiled
  `<<<` and `^` on `Nat` call GMP (Plan.md §6).
* Top-level theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; list them
  in `scripts/axioms.lean`.
* A requirement or theorem that cannot be met as stated is never weakened silently: record
  the obstacle in the ledger and split the task.
* Every public `def`/`structure`/`theorem` gets a docstring; each file starts with a `/-! -/`
  module doc citing the Plan.md section and the T.800 annex/clause it implements.
* Tests: suites in `Tests/*.lean` exposing `run : IO Nat` (number of failures), registered in
  `Tests/Main.lean`.
* Python scripts use only the standard library, run with `python3 -I`, and skip cleanly when
  an external tool (`opj_decompress`, `opj_dump`, `kdu_expand`) is missing. Downloaded files
  are verified by SHA-256; never run an interpreter from inside a downloaded directory.
* Reusable lessons go into the ledger's Gotchas; design changes into its Decisions (and into
  Plan.md only with the human's agreement).

## Attribution

Commits end with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>` (or the line the
session gives); PR bodies end with
`🤖 Generated with [Claude Code](https://claude.com/claude-code)`.
