# The process in the vault

On 2026-11-06 the swarm that builds obend got a workspace that is an obend vault: `~/dev/obend-swarm`
(its own git repository; `obend open`). This page says how `PROCESS.md`'s machines run there, what the
vault decided by itself, and what is still missing. What the vault refused while it was being built
is `~/dev/obend-swarm/FINDINGS.md` (43 entries); the walkthrough that reproduces it on a fresh copy,
and is a gate on obend, is `~/dev/obend/lean/tests/vault/SWARM.md` (28 steps).

## What is in it

- **A page per lane** (`lanes/<branch>.md`, kind `lanes/_kind`): branch, agent (the cv id), brief,
  briefed-at (the root's message), worktree, state (briefed, running, reported, merged); a report adds
  the lane commit, the gate that passed (the command and the success lines its output showed) with the
  root message that shows it, and the doctrine counts read from the lane's own commands; a merged lane
  adds the dev commit and whether it is an ancestor of dev. The kind's laws refuse a report without a
  commit or a gate, a merged lane without its dev commit, a running job without a PID file, and a lane
  that names a box carrying no builds or not answering.
- **A page per brief** (`briefs/`), verbatim from the root's transcript: a brief was a message, not a file.
- **A page per box** (`machines/`: mac, hbox, bb2, persvati, forge, workhorse) with the facts probed on
  the day and the box's rules: fields the lanes' laws read (`nobuild`, `unreachable`) and the box's own
  law over the jobs it lists (`pidfile` on hbox and bb2, `nobuild` on forge and workhorse).
- **The coordinator's seat** (`seats/root.md`) with its doctrine counts.
- **DEV.md**: the lanes merged on dev, each read through its link (merged, dev commit named, ancestor).
- **QUESTS.md**: each brief and the lane page that answers it.
- **Reasons** (`obend reasons status` in the vault): observations are lines of the day's probes, of
  MACHINES.md, of the root's messages and of the doctrine table; competing explanations; proposed
  actions admitted while their justification holds.
- **The doctrine as a genealogy** (`doctrine/`): the rules of 2026-11-05 as floors over the day's
  tallies, a succession for today's rule, refused successions that drop or loosen a rule.
- **A declared fork per lane** (`~/dev/obend-swarm.forks/<branch>`): the lane's report is written in its
  fork and comes back as a merge judged at the tip.

It was built from the record, not by hand: `tools/extract.py` reads the root's and every sub-agent's
transcript through `cv show --json` and dev's first-parent merges from git; `tools/populate.py` writes
the pages in the order things happened (each brief a page and a fork, each merge a report in the fork,
a merge at the tip, the lane marked merged, DEV extended); `tools/finish.py` adds the reasons, the
genealogy and the end-of-day forget. Every command and what the vault said is in `log/`, every
command's time in `data/costs.tsv`.

## How the machines of PROCESS.md run there

| PROCESS.md | in the vault |
|---|---|
| quest Scoped (Q1) | a lane page `briefed`, its brief a page, its fork declared |
| quest Built, Wired, Toothed (Q2 to Q4) | the lane's report in its fork: commit, gate, doctrine counts; the lanes kind refuses a report with no gate, by name |
| quest Landed (Q5) | the fork merged at the tip; the page `merged` with its dev commit; DEV's laws over its links |
| segment, with its machine | the lane page names its boxes; a box that is down or carries no builds refuses it |
| Stomped, SideBranched, Slow (sinks) | the doctrine counts on each lane page and seat, read from the commands; the genealogy's floors over their tallies |
| Reground, G4 (doctrine rewritten, never appended) | a succession of the genealogy: dropping or loosening a floor is refused by name, a new floor admitted |
| Lost, Stalled (sinks) | reasons: an observation with its line, explanations competing, an action admissible only while supported |
| Recorded (Q7) | the vault's log; the end-of-day forget under a retention contract, refused while a lane is out |

## What the day showed

- Four of the day's 33 merges are on dev without a gate the transcript shows passing (one with its
  post-merge build red); the vault refused to record them as merged.
- The coordinator committed another session's files with `git add -A` six times; seven lanes and
  today's lane-holetyping built the whole tree on the Mac. The rules held as floors refuse those tallies,
  but only after the fact: nothing judged the command before it ran.
- MACHINES.md's fact about bb2's clone was stale, and a brief repeated it; persvati was down. Both came
  out of the reasons, not of a law: a law on a box's page would have refused the page that records the
  fact.
- Using the vault at the swarm's size is slow: 206 commands took 1,116 s; one open of four pages took
  three minutes on a 14.7 MB log; `obend log` did not finish in fifteen minutes; the forget that would
  compact the log is refused all day because a lane is always out. lane-cost holds that work.
- Five defects of the vault were fixed on obend's `lane-swarmvault` with their theorems or walkthrough
  steps: a label law that admitted its absence; commit hashes and gate lines silently dropped; two
  suggestions that offered fake values; a merge that lost a refused write.

## Closed on 2026-11-06 (lane-seams)

- **A brief is a form; a report is its fill.** `obend brief PAGE FORM --for LANE --grant PAGE --set
  state=reported --hole commit:label --hole gate:text --hole leftout:text`; the lane fills it where it
  works (`obend fill`), and `obend judge` lands the fill as one turn judged by the lane page's laws. A
  report without a gate is refused by the lanes kind's `gate` law, by name. In the swarm vault, the
  reports of lane-holetyping and lane-cost landed this way.
- **DEV reads its backlinks.** `law listed: linked_by.state == "merged" implies linked_by.listed == 1`
  on DEV: every lane marked merged is listed there, refused at the lane otherwise; DEV cannot drop a
  merged lane.
- **Writes that need each other land together.** The writes an open refused are judged again as one
  turn: pages born linking each other, or a lane marked merged with DEV listing it.
- **A refused write is an exit status.** Every command whose write is refused says so on stderr and
  exits 1; the walkthrough runner holds every refused step to it.
- **The four merges of 2026-11-05 are gated after the fact,** each page saying `gated: after` and the
  dev commit its gate passed on; DEV lists all of dev's merges of the swarm.

## Closed on 2026-11-12 (Shard S5 & Chasm C5)

- **Sharded Merkleized checkpoints (`Obend.Vault.ChunkedWorld`).** 128-bucket `cSHAKE256` sharded
  world storage (`Replay.sharded_checkpoint_is_cache` proved unconditionally): 20,000-page single-page
  `land + write` drops from `1,812 ms` (`15.58 MB`) to `65 ms` (`101.6 KB`), `.obend/checkpoint`
  drops to `8.7 KB`, and unchanged `open` writes `0` shard files.
- **A merge replays a fork's turn atomically (`FINDINGS 41`).** `Branch.merge` and `Merge.mergeVault`
  replay multi-page interdependent writes as a single turn (`merge_is_pushout`, `merge_vault_agrees`).
- **Authority in a fork (`FINDINGS 12`).** `obend fork` and `obend branch` accept `--for MEMBER`,
  judging fork writes against that member's standing grants and revocations at merge tip.
- **Typed link roles, `Reasons`-routed telemetry, doctrine `Genealogy`, and `LawDial` repair
  (`Obend.Vault.SwarmLedgerSeams` & `Obend.Reasons.UnifiedEquilibrium`, landing in Wave 3.7).**
  Role-qualified link laws (`FINDINGS 6, 8`), dead-box / floor-breach observations routed into
  `Reasons` defeaters without refusing factual telemetry (`FINDINGS 14, 20`), `vaultDoctrineHabitat`
  enforcing monotone `Reground` (`G4`) floors (`FINDINGS 19`), and complete multi-field `LawDial`
  witness synthesis.

## What remains to wire into the live CLI workflow

1. **Root gate fills on merge (`FINDINGS 38, 43`).** Merging a lane into `dev` should record an
   `obb broker` / `obb judge` gate fill written by the coordinator's own run.
2. **Git ancestry as an environment fact (`FINDINGS 9`).** `ancestor: true` should be supplied by an
   authenticated `obb` git probe rather than an external script.
3. **Direct `obb` $\to$ Vault ledger emission (`DESIGN.md` §3).** Now that 20,000-page Vault writes
   complete in `65 ms`, `obb` segment and evaluator transitions can emit directly into the swarm
   vault alongside `cv` transcript citations.
