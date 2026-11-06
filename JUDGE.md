# The process's judge, as a genealogy

`~/dev/obend/lean/Obend/Judge/Genealogy.lean` (lane-genealogy, 2026-11-05) states svenvs's gate
over obend's judge: a judge is a value (formats, floors, a checker, a basis); an action is admitted
when its format is the judge's and every floor is discharged; a successor judge is an action the
current judge checks: every floor kept, every floor discharged on every format, `revert` admitted by
theorem, and no trust base beyond the current judge's unless the step is labelled with it (the Löb
cost, carried as the hypothesis `LobCost` and listed by the census). `succession_sound` and
`run_floors` say the genesis floors hold along any chain and any run, whatever the actor; the
walkthrough is `lean/tests/judge/GENEALOGY.md`. This page says what each piece is in obebuilder's
process (`PROCESS.md`), and which pieces do not exist yet.

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
| `Method.eval kernel` / `compiled` / `external who` | a floor decided in the Lean kernel (*decided*), by compiled code or a re-checked artifact (*certified*), or by a model's or a person's review (*attested*): `DESIGN.md` §2.5's regimes are the trust bases |
| non-regression | G4 made a check: a doctrine rewrite that drops a lint, or loosens one (a floor is compared as data, so `cap 1000` is not `cap 100`), is refused naming it |
| a judge succession | Reground's doctrine rewrite, a new lint, a lint moved from the census to `obb lint`, a new evaluator |
| a stronger successor, labelled | adopting a discharge the current process cannot check: a lint run only as compiled Rust, a new model family's review as a floor's discharge. Admitted only with the ledger row naming the principle it rests on; every claim downstream carries that row |
| `cage_not_inhabitant` | a segment's verdict depends on its change and certificate, never on which model or family produced it or what its summary says (the Theater, Label and Ritual sinks are this theorem's failures) |

## What does not exist yet

- The process's judge as a value. Its floors live in four places as prose and code
  (`Obend/Census.lean`, `tools/build.sh`, `~/swarm/RULES.md`, `PROCESS.md` §2) with no single list a
  succession could be checked against. The first `obb lint` should read one `judge.json` in the shape
  `obend genealogy` reads, and the census should be generated from it.
- The habitat for the repository: `Habitat.State` as (commit, ledger), `step` as applying a landed
  diff, and `proved` (which kinds of change keep which floors) with its proofs. The record habitat in
  `Genealogy.lean` is the instance that exists; none is stated over git.
- `revert` as a checked obligation over git: that every landed commit reverts cleanly is assumed by
  Q5, not checked.
- A succession checker over doctrine diffs. G4 is prose ("rewrites sections rather than appending");
  a doctrine rewrite is not yet a proposed `Gate` that the current one judges, so a lint can still be
  dropped by an edit nobody judged.
- The ledger as the chain: each admitted succession and its labels as a ledger row, and the chain's
  Löb cost readable from the ledger (today `LobCost` is counted only in the Lean census).
- Workstream 9's landing condition: a self-modification of the harness, or of obend's kernel, admitted
  by the current judge with a machine-checked non-regression. The checker and its theorems exist; the
  harness and the kernel are not yet habitats.
