# AGENTS

`cairn_json`: a total JSON parser and encoder in pure Lean for
[Cairn](https://github.com/iamnbutler/cairn) apps, with proofs. A Cairn package (`cairn.toml`, registry name `cairn_json`,
claim scope `cairn_json`) that requires `cairn` from the registry. No Swift product, no
`@[extern]`. Read README.md for what is proved and docs/trusted.md for what is only fuzzed.

## Rules

Cairn's rules apply (cairn's AGENTS.md, "Rules" and "Writing Lean"):

- **No `sorry`, no new axioms.** `make check` audits every theorem's axioms; only `propext`,
  `Classical.choice` and `Quot.sound` are allowed.
- **Banned:** `partial def`, `implemented_by`, `extern`, `debug.skipKernelTC`, `native_decide`,
  `bv_decide` and `axiom`. `make lint` greps for them; `make kernel` replays every declaration.
- **Total and pure.** Everything here is a total function with no `IO`, and nothing imports
  `Lean` (apps link it).
- **Toolchain** = Cairn's (`lean/lean-toolchain`). Bump it with Cairn's.
- Ids are the contract: `claims.lock` is written by tools, never by hand.

## Toolchain

`export PATH=$HOME/.elan/bin:$PATH` if `lake` is missing. `make build`, `make check` (lint,
build, axiom audit, kernel replay), `make fuzz` (the trusted comparison with Foundation).
`lake update` needs `RESERVOIR_API_URL=https://cairn.registry.nexthub.sh/api/v1` to resolve
`require "iamnbutler" / "cairn"` from the registry.

## Workflow: lane

Every change happens in a lane, never in the main checkout and never with a bare
`git worktree add`.

1. `lane new <name>` from an up-to-date main, then work in the printed tree.
2. `lane why <path>` before editing a file.
3. Commit as you go. Add a `Why: <path> | <note>` trailer only for a non-obvious constraint.
4. `lane check`; confirm, replace or retire stale notes.
5. `make check` passes.
6. `lane push`, then `gh pr create`. Check `git log --oneline -2` after pushing: the lane must sit
   on current `origin/main`.
7. Squash-merge (`gh pr merge --squash`, no `--delete-branch`), `git pull --ff-only` in the main
   checkout, `lane prune --dry-run`, then `lane rm <name>` for merged lanes prune misses. Never a
   bare `lane prune` while other agents may have lanes open.

<!-- lane:protocol -->
## Context memory

- Before editing a file, read `.lane/memory/<path>/` if it exists, or run `lane why <path>`.
- Record non-obvious findings with `lane note add <path> -a <anchor> "..."`.
- Do not edit `.lane/` by hand; landing manages it.
- Land with `lane merge`, or `lane push` where trunk is protected, then `lane prune` once it merges.
- Detailed workflow lives in `.agents/skills/lane/SKILL.md`; run `lane install skill` if it is absent.
<!-- /lane:protocol -->
