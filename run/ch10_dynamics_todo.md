# Chapter 10 Dynamics TODO

Last updated: 2026-02-10
Target: publication-grade Chapter 10 (standalone, rigorous, human voice, auditable)

## Pass Plan

- [x] Pass 0: Compile sanity and baseline notation checks
- [x] Pass 1: Structural rewrite to standalone paper-style chapter
- [x] Pass 2: Voice/humanization pass (`src/tests/agent-humanize.md`)
- [x] Pass 3: Mechanical notation/format checks (`src/tests/check-math.md`, `src/tests/check-format.md`)
- [x] Pass 4: Line-by-line reviewer pass (`src/tests/agent-reviewer.md`) with explicit issue log
- [x] Pass 5: Deep rewrite for stronger opening, Lean history, and explicit limitations
- [x] Pass 6: Full line-by-line re-audit after rewrite (`run/ch10_line_by_line_review.md` regenerated)
- [x] Pass 7: Compile and final consistency gate
- [x] Pass 8: Three-run `agent-reviewer` scoring cycle with fixes (`run/ch10_agent_reviewer_runs.md`)
- [x] Pass 9: Three-run `agent-writer` quality cycle with iterative prose fixes (`run/ch10_agent_writer_runs.md`)

## Live Checklist (Line-by-Line Quality)

- [x] Opening paragraph has standalone motivation and clear tension
- [x] Chapter frame is independent of previous chapters
- [x] Lean primer includes kernel/elaborator/tactic/definitional equality and practical usage loop
- [x] Lean limitations are stated honestly (elaboration, coercions, typeclass pain points)
- [x] Historical framing includes Hilbert and HoTT/univalent arc with citations
- [x] Motivation includes why formalization changes mathematical workflow and accessibility
- [x] Trust-boundary framing is explicit and auditable
- [x] Quantitative scope claims match repository counts
- [x] Case studies map to concrete theorem artifacts
- [x] Axiom ledger counts match codebase
- [x] AI protocol separates exploration from acceptance and enforces dependency audits
- [x] Prior work section has relevant and accurate citations
- [x] Notation checks pass against `src/tests/check-math.md`
- [x] Reviewer score target achieved (>=8 across dimensions)
- [x] Writer-gate outcome achieved (all non-negotiable outcomes PASS)

## Issue Log (Open)

1. Chapter 10 claim-map table still has minor non-fatal layout warnings due dense typewriter identifiers.

## Exit Criteria

- [x] No factual mismatches against Lean artifacts used in chapter claims
- [x] No notation violations from `check-math.md` rules in chapter prose
- [x] Reviewer-grade verdict: no critical issues, no significant unresolved issues
- [x] Chapter compiles cleanly (non-fatal layout warnings allowed but documented)
