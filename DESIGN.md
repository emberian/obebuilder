# obebuilder: design

Started 2026-11-04 after reading every prompt ember sent to Gemini, Codex and Claude about obend
(Oct 29 to Nov 4) against the tree those prompts produced, then the 2025–2026 literature on
harnesses, multi-model collaboration and slop (`~/paperbin`, `reads/` in the session scratchpad;
sources listed at the end). Revised the same day after ember's objection to the first draft: the
first draft was a task tracker with gates and too many rules; agents do not need to be separate
processes, and the unit of work is a transcript segment, not an agent.

## 1. What went wrong, in one sentence

Three frontier families produced large volumes of work that satisfied the words of the brief
("soundness theorem", "0 sorry", "golden fixture passes") while specifying nothing about the world,
because nothing in the process required a referent outside the author's own definitions and nothing
measured vacuity. obebuilder is the process that would have refused that, made executable and kept
light.

## 2. Principles (each with the source that earned it)

1. **The transcript segment is the unit.** Fork at a message, continue with another model, run two
   or three continuations, keep the best, merge back. `cv splice`, `cv rewind`, `cv distill` already
   do the operations; obebuilder schedules them. Handoffs are directional (Ganz et al. 2026, "the
   handoff tax"): a strong model's prefix guides a weaker continuer, so downshift with the full
   transcript; a weak model's prefix burdens a stronger one, so escalate with the prefix compacted
   or removed and the working tree kept.
2. **Forget on a cadence, keep the artifacts.** Long single trajectories fixate (context inertia:
   Anthropic's Memento, Microsoft's Fork-and-Flush, Tan et al.'s "Scaling Discovery Requires
   Forgetting"). A segment has a length; at its end the next segment starts from the repository and
   a short note, not from the conversation.
3. **Populations, not pipelines.** A spec section, a theorem statement, a module or a brief has
   variants; critiques attach to variants (TextGrad); an evaluator picks (AlphaEvolve, ShinkaEvolve:
   program database, parent sampling, novelty rejection; the AI co-scientist's pairwise tournaments).
   Convergence means no variant beats the incumbent, not "a review round changed nothing".
4. **Mixture before adversary.** Every family drafts; each then sees the others' drafts
   (Mixture-of-Agents: models improve when shown other answers, even weaker ones); then one
   adversarial pass in a fresh context. Family diversity is a weight on who critiques, never a
   prohibition.
5. **An oracle is required to claim, not to start.** Exploration runs without one. What a segment
   may assert at its end is labelled by regime, in obend's own vocabulary: *decided* (an oracle
   outside the author agreed: measurement, reference tool, published benchmark, independent
   derivation, the operational semantics for calculus work), *certified* (a checkable artifact
   exists and was re-checked), *attested* (someone said so). Lints decide which label a theorem or
   claim may carry. The five artifact kinds of Gunter–Jackson–Zave (W domain knowledge, R
   requirement, S specification, P program, M platform) are tags the lints and ledger use.
6. **Enforcement is lints with remediation text, not gates or prose rules** (OpenAI "Harness
   engineering": invariants mechanically enforced, a doc-gardening agent, golden principles as
   garbage collection; Anthropic July 2026: fewer rules, interfaces instead of examples, progressive
   disclosure). The vacuity lints: closed-decide theorems, projection proofs, `golden/verified/poles`
   names, checkers with no tooth on themselves, `.obend` claims restating their method, reverse
   tests (a tooth must bite the checker; an agent's test must fail on the pre-patch code, after
   FrontierCode), scope of a diff, build time per module, the `atp-checkers` suite from the 2026 Lean
   dataset-defects paper.
7. **Coordination through the repository and a supervisor, not locks and nudges.** Kyars's
   six-agent SQLite run spent 54% of its commits on claim locks; Gas Town coordinates by prose over
   tmux. The alternative is the OTP shape: segments are processes under a supervisor, restart from
   artifacts on failure, budgets per segment, worktrees, PID files, stacked small diffs into a merge
   agent, and the repository as system of record (anything not in it does not exist to the agent).
8. **Human attention goes where the leverage is**: research, plan, theorem statements, briefs; code
   only where the person cares (Horthy, "Why Software Factories Fail": a bad line of research costs
   thousands of lines of code). Vertical slices over horizontal layers.
9. **Size the ceremony to the work** (Böckeler on spec-driven tools; Huang's Paxos). Most work is
   one segment and one review; medium work gets one plan; only large things get the population
   treatment. Effort defaults to medium (SlopCodeBench: xhigh bought no strict passes at 2 to 4 times
   the cost).
10. **Briefs are induced from transcripts** (Agent Workflow Memory). Successful segments in `cv` are
    mined into reusable workflows; new briefs start from those, written as a colleague's note.
11. **Claim labels in every note.** VERIFIED / SOURCED / INFERRED / PROPOSED / CHAT-REPORTED /
    REJECTED, as in `~/dev/degg-research` and `~/dev/zkml-research`, whose `docs/VERDICTS.md` is the
    single-truth-file discipline obend's record lacked.

The control flow these principles imply is `PROCESS.md`: three nested statecharts (campaign,
quest, segment), guards computed from the Lean environment, cv and git, and one sink per
frustration that persisted across the prompt corpus (`~/dev/collected-writings/prompts/COHERENCE.md`).
`spec/process.json` is the machine form.

## 3. Objects

- **Segment**: (parent segment or none, model, effort, brief, worktree, machine, budget, start,
  end, outcome, regime of its claims, agent id in `cv`). Operations (`obb seg`): `new`, `continue`,
  `distill`, `fork`, `merge`, `forget`, `adopt`, `compare`, `list`.
- **Artifact**: a spec section, statement, module, brief, or note, with a content hash, a kind tag
  (W/R/S/P/M), a regime label, and a population of variants each carrying its critiques and
  evaluator results.
- **Evaluator**: an oracle (measurement, reference tool, benchmark, independent derivation,
  semantics), a lint, a rubric with calibration cases, or a tournament.
- **Ledger**: append-only rows (segment or artifact, event, by whom, when, reason, evaluator
  result). An open decision for ember is a row that blocks what cites it. When obend's vault tooling
  is fast enough to be depended on, the ledger becomes an obend vault with laws judged on write.

## 4. Executors

- Claude: `claude -p`, Agent SDK, Workflow.
- Codex: `codex exec` and its native multi-agent (see memory note on codex 0.162).
- Gemini: `agy --print --output-format stream-json`, `--input-format stream-json` for a turn per
  NDJSON line, `--conversation <id>` to resume, `--model`, `--effort`, `--json-schema`,
  `--dangerously-skip-permissions`; transcripts also ingested from `~/.gemini/antigravity-cli/`.
- Machines from `~/swarm/MACHINES.md`; `swarm-build` on hbox; one build per tree; disk pressure
  pauses the scheduler.
- Transcripts indexed by `cv`; a segment's page links its agent id.

## 5. The visualizer

`obb serve` on localhost: segments as a tree with states, runtime, retries, budget use, machine
load; artifacts with their populations and evaluator verdicts; a "ready" column and a "waiting on
ember" column; server-sent events. An unseeded vault opens empty (`0` live transitions) unless
`--seed-demo` is passed explicitly, and `StateSnapshot` separates `live` verified quests and
`AttestedOverride` emergency merges from `demo_seed` fixtures. This is how a person follows forty
segments without reading forty transcripts (after Luke Hutchison's Zed plan page).

## 6. Shape and landed engines (`obb v8`, `0.8.0`)

Rust 2024 workspace of seven crates (`obb-core`, `obb-lint`, `obb-judge`, `obb-quarry`,
`obb-state`, `obb-broker`, `obb-cli`), one binary `obb` with thirteen top-level commands (`lint`,
`cone`, `apex`, `pipeline`, `harness`, `broker`, `quarry`, `judge`, `state`, `seg`, `ledger`,
`serve`, `verify-transport`):

1. **`obb lint` & `obb harness` (`obb-lint`)**: Vacuity, `atp-checkers`, uninhabited-premise,
   `Judge.Fragment` operational-check restatement (`lean/judge-fragment-restates-check`),
   Pigeonhole/Minkowski vacuous cryptographic hardness & unkeyed `Prop` collision disjunctions
   (`lean/pigeonhole-vacuous-premise`), cross-language `Rust ↔ Lean` domain-tag & static framing
   arity drift (`cross-lang/domain-tag-drift`), 3-way proof/test/mutation separation
   (`lean/test-in-library` under `--strict-tests` + always-on `tier1_guards` / `tier1_teeth` /
   `tier1_evals` telemetry), `native_decide`, narrow-digest-weld (`< 128` bits),
   Lean 4.35 module-hygiene rules (`lean/file-wide-expose`, `lean/public-meta-import-leak`),
   `.obend` claim checks, process sink detectors, typeclass/structure compositionality indexing,
   and cross-agent `AGENTS.md` / `GEMINI.md` / `CLAUDE.md` harness parity (`obb harness`).
2. **`obb cone` & `obb apex` (`obb-lint`)**: `< 25 ms` parallel Lean module-header DAG analyzer and
   disjoint shard planner (`obb cone plan`, isolating high-fan-in barrier hubs), paired with
   whole-system Apex theorem reverse-cone coverage and leaf-island detection against
   `quarry/obend-apex.toml`.
3. **`obb pipeline` & `obb judge` (`obb-judge`)**: Two-stage `[HypothesisLedger]` / `[Obligations]`
   interface-lock (`STAGE_A_LOCKED`) and non-vacuous instance-seal (`STAGE_B_SEALED`) swarm gate,
   plus `Genealogy`-style monotone floor judging (`g0-obebuilder` self-hosting floors), isolated
   `/private/tmp` `#tooth` (`planted_fault_red`) negative-control execution (`BIT`, `VACUOUS`,
   `INVALID_TOOTH`, `POSITIVE_FAILED`), fail-closed `UnknownFloor` / `MissingMeasurement`
   diagnostics, honest `eval:lexical` (*attested*) vs `HEAD`-bound `KernelReceipt` (`eval:kernel`,
   *decided*) regimes, and HMAC-authenticated, SHA-bound `JudgeReceipt` issuance (`--base`,
   `--emit-receipt`). Opt-in floor/tooth input cones reuse authenticated verdicts from
   `.obb/cache/cones/`, keyed by git input OIDs, check definitions, and the evaluator executable.
   Dirty trees bypass reuse; history and external evidence retain their own freshness checks.
   File-unit gates can export the committed file view, modes, Merkle root and runtime fingerprint in a wire-v2 receipt.
   `obb verify-transport` authenticates this evidence against another tree. See `JUDGE.md` for the wire format and key selection.
   A repository without obligation classes seals only through its own verified Apex manifest. Every
   pipeline report names its `ledger_basis`, and a seal produced by `--allow-empty` is reported as `allow_empty_override`.
4. **`obb quarry` (`obb-quarry`, `obb-cli`)**: Zero-pollution `refs/quarry/*` donor git-history
   synchronizer and 6-gate pre-uptake surgery inspector driven by `quarry/obend-quarry.toml`.
5. **`obb broker`, `obb state`, `obb seg`, `obb ledger` & `obb serve` (`obb-broker`, `obb-state`)**:
   ZFS-ARC-aware SSH probe and CoW/reflink (`cp -R --reflink=auto`) `.lake/build` seed-pool router
   across `bb2` and `hbox` with `0700` per-invocation worktrees, hard wall-clock and RSS reapers,
   receipt-verified quest lifecycle (`take` with non-overlapping footprint leases, `propose`,
   `land` with TOCTOU `StaleBaseSha` enforcement and exact proposed candidate/receipt binding,
   and `AttestedOverride` emergency bypass logging). Committed pure deletions are valid
   `Built`/`Wired` artifacts; missing or uncommitted files are not deletion evidence. The supervisor also provides a
   segment handoff-tax & pressure statechart, SHA-256 hash-chained JSONL ledger, and live SSE
   dashboard. `/api/lints` runs the target repository scanner in `spawn_blocking` on each
   request, including local edits and untracked files. Responses expose `source: "live"`,
   `scanned_at`, and count deltas against a matching repository baseline when present;
   a committed baseline is never served as a current scan.
6. **Multi-family Mixture-of-Agents (`Principles 3 & 4`)**: Parallel Round-1 population drafts
   across Gemini (`agy`), GPT-6-Astra (`codex exec`), and Claude-Fable-5.2 (`claude -p`) armed with
   `~/swarm/research.py` and `~/paperbin`, followed by Round-2 cross-family synthesis before Wave
   commits.

## 7. What this is not

Not a way to run more agents; a way to run fewer with a referent each and to splice their work. Not
a workflow for every size of task. Not obend-specific in its core; obend-specific only in its lint
plug-ins and its ledger.

## Sources read for this design

Gunter, Gunter, Jackson, Zave 2000; Zave and Jackson 1997; Parnas and Clements 1986; Oberkampf,
Trucano, Hirsch 2004; Salari and Knupp 2000; Ringer et al. 2019; Klein et al. 2014; Kupferman and
Vardi 2003 (not fetched, 403); the 2026 Lean dataset-defects audit (arXiv 2606.29493); Ganz et al.
2026 (arXiv 2608.24358); Fan et al. 2026 (arXiv 2609.20804); Ning et al. 2026 "Code as Agent
Harness" (arXiv 2605.18747); ATC (arXiv 2611.04321); AgentDiet (arXiv 2509.23586); Mixture-of-Agents
(arXiv 2406.04692); Co-LLM (arXiv 2403.03870); TextGrad (arXiv 2406.07496); ShinkaEvolve (arXiv
2509.19349); AlphaEvolve (arXiv 2506.13131); AI co-scientist (arXiv 2502.18864); Agent Workflow
Memory (arXiv 2409.07429); Du et al. 2023 debate; MetaGPT; Horthy "Why Software Factories Fail" and
"Advanced Context Engineering" (humanlayer); OpenAI "Harness engineering" (Feb 2026); Anthropic
"Effective harnesses for long-running agents" (Nov 2025) and "The new rules of context engineering
for Claude 5" (Jul 2026); Breunig "The State of Context Engineering" (Oct 2026); Appleton on Gas
Town; Yegge's Beads; Kyars "building sqlite with a small swarm"; Guimarães on Elixir; Cognition
FrontierCode; SlopCodeBench (Oct 2026); dollspace-gay's VSDD gist; Huang "100K lines of Rust with
AI"; Böckeler on Kiro, spec-kit and Tessl; Willison on parallel agents.
