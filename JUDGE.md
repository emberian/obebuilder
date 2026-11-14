# The process's judge, as a genealogy

`~/dev/obend/lean/Obend/Judge/Genealogy.lean` (lane-genealogy, 2026-11-05) states svenvs's gate
over obend's judge: a judge is a value (formats, floors, a checker, a basis); an action is admitted
when its format is the judge's and every floor is discharged; a successor judge is an action the
current judge checks: every floor kept, every floor discharged on every format, `revert` admitted by
theorem, and no trust base beyond the current judge's unless the step is labelled with it (the Löb
cost, carried as the hypothesis `LobCost` and listed by the census). `succession_sound` and
`run_floors` say the genesis floors hold along any chain and any run, whatever the actor; the
walkthrough is `lean/tests/judge/GENEALOGY.md`. This page says what each piece is in obebuilder's
process (`PROCESS.md`), what `obb v7` (`0.7.0`) enforces mechanically, and which Lean proofs remain.

## The mapping

| genealogy | obebuilder |
|---|---|
| habitat state | the repository at a commit on `dev`, with the ledger and the doctrine files |
| action, in a format | a segment's landed change (quest state Landed), proposed in a registered format: an obend `Judge.Format` from `Obend.Judge.registry` (`lrat@1`, `impact@1`, `judge-succession@1`, …) whose object is the claim the change makes and whose certificate is checked, never searched for |
| floor | a decidable property every landed change keeps: the census (no `sorryAx`, no declared axiom), the tier-1 time budget and heartbeat baseline, the docs census, every walkthrough green, every planted mutant red |
| the corrigibility floor `home N` | ember can bring the tree back within a bounded horizon: every landed change is a named-files commit that reverts cleanly, every detached job has a PID file, disk pressure pauses the scheduler |
| `revert`, admitted by every judge | `git revert` of a landed commit, and stopping a job by its PID file; no judge may refuse them, and no change may be admitted that makes them fail |
| `forget`, the one-way door | history rewriting, `git stash`, force pushes, deleting outside the scratchpad, a kill by pattern: refused because they move home |
| the checker (`methods`) | the harness lint: per format and floor, how the floor is discharged |
| `Method.lemma` | a theorem that a kind of change keeps a floor (a docs-only change keeps the census), so the lint is skipped by proof, not by trust |
| `Method.eval kernel` / `compiled` / `external who` / `lexical` | `eval:kernel` (*decided*) requires a `HEAD`-bound external kernel receipt (`.obb/kernel-receipt.json` from `lean4checker` / Lean kernel replay); `eval:compiled` executes isolated `/private/tmp` negative controls (`planted_fault_red`: *decided* when every `#tooth` bites `BIT`, distinguishing `VACUOUS`, `INVALID_TOOTH`, and `POSITIVE_FAILED`) or native timing/heartbeat caps (*certified*); `eval:external:<tool>` (*certified*) checks an external tool (`git merge-tree`, `lean-transport`); `eval:lexical` (*attested*) runs static token/AST rules (`no_sorry_ax`, `no_declared_axiom`, `docs_symbols_exist`, `tooth_structural_presence`) and fails closed if mislabeled `eval:kernel` |
| fail-closed evaluation | unknown floor names or caps fail closed with `UnknownFloor`, and missing timing (`.obb/build-timings.json`) or spec-sensitivity (`.obb/spec-check.json`) artifacts fail closed with `MissingMeasurement` — never defaulting to `0` |
| non-regression | G4 made a check (`obb judge succeed`): a rewrite that drops a floor, loosens a numeric cap (`<= 60` to `<= 600` or `home 10` to `home 5`), or drops `revert@1` is refused naming it |
| a judge succession | Reground's doctrine rewrite, a new lint, a lint moved from the census to `obb lint`, a new evaluator |
| a stronger successor, labelled | adopting a discharge outside `basis` requires `--lob <trust>` and records `LobCost` in `<state_dir>/events.jsonl`; unlabelled expansion is refused (`Stronger`) |
| `cage_not_inhabitant` | a segment's verdict depends on its SHA-bound `JudgeReceipt` (`(gate_sha256, base_sha, head_sha, tree_oid)`), never on caller self-attestation or which model family produced it |

## Landed in `obb v7` (`0.7.0`) vs what does not exist yet

- **Landed in `obb-judge` and `obb-state` (`0.7.0`)**:
  - `judge.json` (`g0-obebuilder`) encodes the repository's judge as a `Gate` value (`formats`, `floors`, `methods`, `basis`, plus `.obb/teeth.json` and `.obb/build-timings.json`), checked by `obb judge show` and `obb judge check --base <rev> --emit-receipt <path>`.
  - `planted_fault_red` executes positive (`exit == 0`) and mutated negative (`exit != 0`) controls inside disposable `/private/tmp` sandboxes without touching the candidate working tree; static/index presence is segregated under `tooth_structural_presence` (`eval:lexical`, `attested`).
  - `home N` corrigibility (`obb judge check-revert`) runs 3-way `git merge-tree --write-tree` in a scratch bare repo via read-only `objects/info/alternates`.
  - `obb judge succeed` enforces G4 floor/cap non-regression and persists `LobCost` succession records to the SHA-256 hash-chained ledger (`obb ledger verify`).
  - `obb state` (`take`, `propose`, `land`) requires verified `JudgeReceipt`s bound to `(base_sha, head_sha, tree_oid)` and non-overlapping footprint leases rather than caller booleans. The SHA-256 `receipt_hash` identifies the evaluation; `receipt_mac` authenticates it with HMAC-SHA256. State verifies the MAC whenever a key is configured, independently re-derives the git facts, and requires the exact proposed `(head_sha, receipt_hash)` before landing and the same landed pair at `Claimed`. Artifact paths must stay inside the repository (no `..`, absolute paths, or symlinked parents). Pure deletions count as artifacts at both `Built` and `Wired` when git confirms them against the quest’s base.
  - Two clocks. `obb judge check --fast` is the construction clock: static floors and recorded measurements only, executed `#tooth` runs and `home N` revert merges listed as `deferred_floors`, result at most `attested`, no receipt (`--fast` conflicts with `--emit-receipt`). Plain `obb judge check` is the convergence clock and runs everything. `obb serve` polls on the construction clock.
  - Input-cone reuse skips unchanged opted-in floors and teeth during convergence. Authenticated verdict entries live in `.obb/cache/cones/<digest>.json`; reused results carry `reused_from_cache: true`.
- **What does not exist yet**:
  - The Lean `Habitat.State` instance over git (`(commit, ledger)`, `step` as applying a landed diff, and machine-checked Lean proofs of `Method.lemma` floor preservation for `revert@1` and path-disjoint edits in `~/dev/obend/lean/Obend/Judge/Genealogy.lean`).
  - Workstream 9's landing condition: self-modification of `obb` and `obend`'s kernel judged directly inside a proved Lean git habitat.

### v7 portable self-check

`cargo test --workspace` and `cargo clippy --workspace --all-targets -- -D warnings`
exercise the Rust workspace. Run `obb judge show`, `obb lint --repo . --strict --strict-tests`,
and `obb judge check --repo . --strict-tests` for the configured self-check.
Neither the structural scanner nor the built-in mutation probe invokes Lean or Lake.

`--strict-tests` checks Rust test attributes (`#[test]`, any `#[<path>::test]`, `#[cfg(test)]`,
`#![cfg(test)]`; `#[cfg(not(test))]` is library code), JS/TS test calls with a literal name
(`describe`/`it`/`test`, including `.only`/`.skip`), Python test definitions
and TestCase references, and Lean test commands in library sources. The scanner keeps
line positions while excluding comments and literals. Tests live in dedicated test files
or directories; the repository's Rust tests and SSH test executor now live under `tests/`.
`judge check --strict-tests` includes all four placement floors in the emitted receipt.

The tracked judge declares a `structural_probe` tooth. It executes clean and deliberately
faulty fixtures through the real scanners for all four languages and for a tautological
Lean Judge meaning. It reports its five controls individually and certifies scanner
sensitivity, not a Lean proof or arbitrary candidate behavior. The separate executable
bedrock tooth checks the gate before and after removing its revert format. Both are in
`judge.json`; ignored `.obb/` artifacts are optional. A tier-1 Lean timing floor is explicitly
not applicable when there are no tier-1 Lean modules; with such modules present, missing
measurements still fail closed.


### Receipt keys and input cones

`OBB_RECEIPT_KEY` supplies literal UTF-8 key bytes (an empty value is an error). Otherwise,
receipt issuance reads `<state-dir>/.obb/receipt.key` when `--state-dir` is supplied, then
`<repo>/.obb/receipt.key`. If neither exists, it generates 32 random bytes in the selected
state directory, or in the repository when no state directory was selected. Creation is
atomic with mode `0600`; an existing key is never overwritten. Use the same state directory
for `judge check`, `state propose`, and `state land`, and ignore `.obb/` in git.
State uses the same precedence, requiring a constant-time MAC check when any key exists.
Legacy hash-only receipts remain usable only where no key is configured. Key rotation
invalidates prior receipts and cache entries.

The MAC covers `receipt_hash`, which hashes the canonical receipt payload, excluding the
hash and MAC fields themselves. The MAC input is domain-tagged: `obb-judge-receipt-v1`, a
NUL byte, then the hash; cone cache entries use `obb-cone-verdict-v1` under the same key, so
a tag for one kind of message never verifies as the other. Recomputing an unkeyed hash after editing a verdict does
not produce a valid MAC. This authenticates possession of the key: mode `0600` does not
isolate processes running as the same OS user. A hostile agent must not be allowed to read
or replace the key or invoke an unrestricted signer. Sandbox copies omit the repository
key and cone cache, and check subprocesses do not inherit `OBB_RECEIPT_KEY`.

Floors accept a configured wrapper around the existing floor syntax:

```json
{"floor": "no_sorry_ax", "inputs": ["lean/"]}
```

The existing structured home/cap objects also accept `inputs`; named floors can use
`{"name": "no_sorry_ax", "inputs": ["lean/"]}`. Teeth accept `inputs` alongside their existing `check_cmd`, `build_cmd`, and mutation.
Literal paths match the path and its descendants; globs support `*`, `?`, and recursive
`**` (including zero directories in `src/**/*.rs`). An empty or omitted list disables
reuse. Input declarations must include every source, test, configuration, and script the
check reads. A custom named floor can also declare a `command` and `timeout_ms` (default
15000); it runs in a disposable copy, passes only on exit zero, and is at most `certified`.
Use `eval:external:shell` and declare `external:shell` in the gate basis. A command cannot
override a registered floor or claim kernel verification. Commands are deferred on the
construction clock.

Cone digests bind sorted git tree entries (paths, modes, blob/tree OIDs), the input patterns,
the evaluator definition (including commands, timeout, and mutation patch), and the running
executable digest. New, deleted, and changed matching paths invalidate the cone; unrelated
commits do not. Dirty worktrees bypass reuse and cache writes. "Clean" means `git status`
(with `core.fsmonitor` forced off) reports nothing and no index entry is `assume-unchanged`
or `skip-worktree`; the same test sets `clean_working_tree` in receipts and the Q5 probe.
A cone is executed, never reused, when a pattern selects no committed path, when it selects
a symlink or submodule, or when an ignored file or directory lies inside it (`.obb/` and
the directories the sandbox copy skips are exempt). `home N` additionally binds
HEAD because it depends on history; kernel and external measurement floors are rechecked.
Reused verdicts preserve their original execution duration and epistemic regime. Cache
entries are authenticated with the receipt signing key when issuing a receipt, so a weaker
repository key cannot authorize evidence for a vault-key-signed receipt. Malformed or
tampered entries are treated as misses. This
is declared-dependency reuse, not proof of cone completeness: external tools, environment,
and network state must be held fixed, or reuse must be disabled for that check.
