# The process in the vault

On 2026-11-06 the swarm that builds obend got a workspace that is an obend vault: `~/dev/obend-swarm`
(its own git repository; `obend open`). This page says how `PROCESS.md`'s machines run there, what the
vault decided by itself, and what is still missing. What the vault refused while it was being built
is `~/dev/obend-swarm/FINDINGS.md` (37 entries); the walkthrough that reproduces it on a fresh copy,
and is a gate on obend, is `~/dev/obend/lean/tests/vault/SWARM.md` (20 steps).

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

## What is still missing

1. **The report as a form.** Forms move numbers between pages and conserve them; a report sets labels
   and text. Until a form has label and text holes and a `set` move, the brief is not a form and the fill
   is a write in a fork (FINDINGS 10).
2. **Authority in a fork.** A fork writes as the owner; the merge does not know which lane wrote, so a
   lane's fork can write any page. A fork declared for a member, its writes judged against that
   member's grants at the tip (FINDINGS 12).
3. **Laws over backlinks and link roles.** A box's laws cannot reach the lanes that name it; "every merged
   lane is on DEV" cannot be said; a lane's law cannot tell its build box from its brief (FINDINGS 6 to 8).
4. **Records of facts that break a law.** A merge without a gate, a box that went down, a tally over a
   floor: each is refused instead of recorded as an inconsistency to resolve (FINDINGS 14, 20). The
   reasons substrate is where such facts belong; the vault's laws do not yet read it.
5. **The judge in front of the command.** The doctrine is two texts (the lanes kind's laws and the
   genealogy's floors) and the genealogy's habitat is a record of naturals, not the vault. The step is a
   PreToolUse judge whose state is the floors' tallies and whose succession is an edit of a kind page
   (FINDINGS 19, 20; JUDGE.md's "What does not exist yet").
6. **Births of mutually linked pages.** A fresh copy of this vault does not open: the lanes and the box
   they build on link each other under laws over links, and none can be born first (FINDINGS 36).
7. **Cost at the swarm's size.** Every command reads the whole log; a merge record carries the fork's
   world; retention cannot compact while lanes are out (FINDINGS 21 to 23).
8. **Git as an environment.** `ancestor: true` is written by a script; no law reads dev's history
   (FINDINGS 9).
9. **cv inside the vault.** The doctrine counts and gate lines are extracted by a script over `cv show
   --json`; the lints of PROCESS.md §2 are not yet a part of `cv` or `obb lint` that writes the pages.
