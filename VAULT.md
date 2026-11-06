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

## What is still missing

1. **A merge replays a fork's turn one page at a time.** Writes a fork landed together are refused at
   the tip one by one, each waiting on another (FINDINGS 41). `Branch.merge` should replay a side's turn
   as a turn.
2. **Authority in a fork.** A fork writes as the owner; the merge does not know which lane wrote, so a
   lane's fork can write any page. A fork declared for a member, its writes judged against that
   member's grants at the tip (FINDINGS 12).
3. **Link roles.** A law over links or backlinks reads every linked page alike: a lane's law cannot tell
   its build box from its brief, and DEV cannot see a merged lane that does not link it (FINDINGS 6, 8).
4. **Records of facts that break a law.** A box that went down, a tally over a floor: each is refused
   instead of recorded as an inconsistency to resolve (FINDINGS 14, 20). The reasons substrate is where
   such facts belong; the vault's laws do not yet read it.
5. **The judge in front of the command.** The doctrine is two texts (the lanes kind's laws and the
   genealogy's floors), and the genealogy's habitat is a record of naturals, not the vault (FINDINGS 19,
   20; JUDGE.md's "What does not exist yet").
6. **Gates the root runs.** The root merged both of today's lanes with no gate of its own, and dev's
   FORMS walkthrough now fails its cost check (FINDINGS 38, 43). A merge into dev should be a fill of
   the lane's brief whose gate line the root's own run wrote.
7. **Git as an environment.** `ancestor: true` is written by a script; no law reads dev's history
   (FINDINGS 9).
8. **cv inside the vault.** The doctrine counts and gate lines are extracted by a script over `cv show
   --json`; the lints of PROCESS.md §2 are not yet a part of `cv` or `obb lint` that writes the pages.
