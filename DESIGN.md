# obebuilder: design

Started 2026-11-04 after reading every prompt ember sent to Gemini, Codex and Claude about obend
(Oct 29 to Nov 4) against the tree those prompts produced. The finding that motivates this tool:
three frontier model families each produced large volumes of work that satisfied the words of the
brief ("soundness theorem", "0 sorry", "golden fixture passes") while specifying nothing about the
world, because nothing in the process required a referent outside the author's own definitions.
obebuilder is the process, made executable.

## 1. The artifact model: W, R, S, P, M

Every unit of work produces one of five artifacts (Gunter, Gunter, Jackson, Zave 2000,
`~/paperbin/gunter-gunter-jackson-zave2000-*`):

- **W** domain knowledge: presumed facts about the environment (a device's physics, a datasheet, a
  benchmark problem's reference answer, a tool's observed behaviour). W is never authored by the
  agent that will be checked against it; it is retrieved, measured, or derived from a reference
  implementation, and cites its source.
- **R** requirement: what we need to be true, stated in environment terms (a field computed from a
  current agrees with FEMM on TEAM problem 24 to within x; a RISC core passes the compliance suite;
  a claim refuses a specific wrong program).
- **S** specification: the interface and behaviour the program must have so that W ∧ S ⊢ R. This is
  where `.obend` claims, Lean theorem statements and `Judge.Format`s live.
- **P** program or proof: the implementation of S.
- **M** platform: Lean, the machines, the toolchain, the build gates.

The proof obligation of the model is W ∧ S ⊢ R. A claim of the form S ⊢ S (a theorem whose
statement and proof are the same definition read twice; a checker tested on a fixture authored to
pass it; a "soundness" theorem that projects a field out of a record) discharges nothing. The tool's
first job is to make such claims impossible to schedule and easy to detect after the fact.

## 2. The unit of work: a node with a referent and an oracle

A node is a TOML record in `plan/`. Required fields:

```toml
[node.magnetics-team24]
title    = "2D magnetostatic solve agrees with FEMM on TEAM problem 24"
artifact = "P"                     # W | R | S | P | M
refines  = ["spec.magnetics.solve"] # the S (or R, or W) this node serves
size     = "L"                      # S | M | L | XL  (wall-clock budget derives from size)
oracle   = { kind = "reference-tool", tool = "femm", problem = "team24",
             tolerance = "2% peak B", source = "~/paperbin/compumag-team-problem24-*.pdf" }
owner    = "claude"                 # family that implements
verifier = "codex"                  # a different family verifies; never the implementer
budget   = { wall = "4h", build_s_per_module = 60 }
after    = ["magnetics-mesh-reader", "w.team24-reference-field"]
```

Oracle kinds, in order of preference:

1. `measurement`: data from the world (a datasheet file, a bench measurement, a tape-out report).
2. `reference-tool`: an independent implementation run on the same input (FEMM, ngspice, devsim,
   yosys/nextpnr timing, Verilator against a published core, RISC-V compliance tests).
3. `benchmark`: a published problem with a published answer (TEAM problems, SPICE benchmark
   circuits, IEEE 754 vectors, MMS manufactured solutions per Salari and Knupp 2000).
4. `independent-model`: a second derivation by a different family from the same W and R, compared.
5. `adversarial`: a generator of inputs the implementation must refuse, written by the verifier.
6. `metatheory`: for S-nodes about the calculus itself, the independent object is the operational
   semantics; the theorem must relate two separately defined things (checker vs. Step, machine vs.
   reference reducer). This is why `Obend/Core` is honest and `Obend/Hardware` was not.

A node with no oracle cannot leave `waiting`. A node whose oracle is "the checker accepts the
fixture" is rejected at lint.

## 3. The spec pipeline before any P-node runs

The spec is a set of markdown sections under `spec/`, each with a stable id and a content hash.

1. **Compile.** From ember's notes, transcripts (`cv`), and the existing design documents, one agent
   compiles a draft per section. Every sentence that asserts a fact about the world is tagged W and
   cites a source or is marked `UNSOURCED`.
2. **Cross-review to convergence.** Each family critiques every section; each family then
   meta-critiques the other two critiques; a merge agent folds the surviving points in. Repeat until
   a round produces no accepted change. Each round is a DAG of nodes, so it is visible and budgeted.
3. **All-pairs consistency.** For every pair of sections (i, j), a node checks for contradiction,
   duplicated authority, or an undefined name used across the boundary. Pairs are cached by the two
   content hashes, so a rerun after an edit costs only the pairs that touched the edited section.
4. **Decomposition.** An agent proposes the P-node DAG: tiny steps, topologically ordered, each with
   its referent and oracle filled in. `obb plan lint` refuses nodes without an oracle, cycles, nodes
   over the size ceiling, and nodes whose `refines` names no spec section.
5. **Freeze.** A spec revision is tagged; nodes record which revision they implement. A spec edit
   reopens exactly the nodes whose sections changed (the hash tells us), the way an obend slot's
   supports do.

## 4. Gates a node passes through

```
waiting ─▶ ready ─▶ briefed ─▶ in-progress ─▶ verify ─▶ measure ─▶ merge ─▶ done
                                   │              │          │
                                   └─ rejected ◀──┴──────────┘   (with the reason, retry counter)
```

- **briefed.** The brief is generated from the node, its spec sections, the real signatures of what
  it depends on (pasted, not described), the oracle, and the standing rules (PID files, swarm-build,
  named-file commits). A second family reads the brief and returns "missing ground truth" or
  "ready". Briefs that shout or prohibit are rewritten (Brief style: a colleague's note).
- **in-progress.** Runs in its own worktree on the machine the plan assigns, under `swarm-build`,
  with a PID file, under the node's budget. Over budget is a red node, not a wait.
- **verify.** A different family reads the theorem statements and the diff, never the implementer's
  summary. It runs the vacuity probes: mutate the implementation and require the theorem to break;
  mutate the fixture and require the checker to refuse; for every `_sound` theorem, state in one
  sentence what the conclusion says beyond the hypothesis. It runs the oracle. It reports CONFIRMED,
  PLAUSIBLE or REJECTED with the inputs that would change the verdict.
- **measure.** Build time per touched module against the ceiling; the one-edit cascade; token and
  wall-clock cost. Numbers go to the node's log, not to prose.
- **merge.** Rebase onto main in the worktree, build the umbrella once, commit named files, append
  the ledger row (what was decided, by which authority, the oracle result).

## 5. Vacuity lint (project plug-ins)

Lint runs on every verify and on demand over a whole tree. Plug-ins are per language; the first two
are for obend:

- **Lean.** Classify every theorem: quantified, closed-decide, closed-other; flag theorems whose
  proof is a projection of a hypothesis (`exact h.1`, `simp at h; exact h.2.1`) and whose
  conclusion names no object absent from the hypothesis; flag `golden_*`, `*_verified`, `*_poles`
  names; flag a checker with no tooth on the checker itself (a tooth on the fixture does not count);
  flag `Meaning := check = .ok`. This extends `Obend.Census` rather than replacing it.
- **`.obend`.** Flag a `claim` whose right-hand side is the body of the method it names; flag a
  `spec` whose every method is a constant or an affine function of its argument with a physical
  name (the "product name on arithmetic" shape).
- Output is the per-directory classification table, never a headline count.

## 6. Executors and the record

- Families: Claude (`claude -p`, Agent SDK), Codex (`codex exec`, its native multi-agent), Gemini
  (Antigravity CLI, when a non-interactive entry point exists; otherwise its sessions are ingested
  from `~/.gemini/antigravity-cli/` and treated as a family whose output arrives by handoff).
- Machines: from `~/swarm/MACHINES.md`; the plan assigns a machine per node; one build per tree;
  disk pressure pauses the scheduler.
- Transcripts: everything an executor does is indexed by `cv`; a node's page links its agent id.
- Ledger: append-only rows `(node, event, by, at, reason, oracle-result)`; a decision ember must make
  is a row of kind `open` and blocks the nodes that cite it. Once obend's own vault tooling is fast
  enough to be a dependency, the ledger becomes an obend vault with its laws judged on write; until
  then it is a markdown table the tool owns.

## 7. The visualizer

`obb serve` on localhost: the DAG with states as colours, per-node runtime, retries, rejections,
budget use, machine load; a node page with its brief, its log, its verifier's report, its oracle
result; a "ready" column; a "waiting on ember" column. Server-sent events for live updates. This is
what lets a person see what forty agents are doing without reading forty transcripts.

## 8. Implementation shape

Rust workspace, one binary `obb`:

- `obb plan lint | graph | ready` over `plan/*.toml` and `spec/*.md`.
- `obb serve` (axum, SSE, a single static page).
- `obb run` (tokio scheduler; executors as trait objects; worktrees; PID files; budgets).
- `obb review`, `obb pairs` (the spec pipeline as generated nodes).
- `obb lint` (vacuity plug-ins; the Lean one shells out to the project's census).
- State in SQLite (`.obb/state.db`); the plan and spec in git; the ledger in git.

First milestone: `plan lint` and `serve` over a hand-written plan for obend's current situation
(the fake list from the 2026-11-04 review as nodes, each with the oracle it lacks). Second:
`run` with the Claude and Codex executors on bb2. Third: the spec pipeline. Fourth: the lint
plug-ins. The ledger moves into an obend vault last, when obend can carry it.

## 9. What this is not

Not a replacement for judgement about what to build; the research questions are still ember's.
Not a way to run more agents; a way to run fewer with a referent each. Not obend-specific in its
core (W/R/S/P/M, nodes, gates, oracles) and obend-specific only in its lint plug-ins and ledger.
