# Tests

Alignment tests for thesis quality control. Tests are agent-executable prompts that evaluate content against specific criteria.

## Purpose

These tests verify that thesis content meets two standards: correctness and quality.

Correctness means notation is consistent, math matches the published paper, and formatting is clean. Quality means the writing reads as it should: each idea arriving when needed, definitions feeling necessary, results stated with precision. For detailed style guidance, see `taste/README.md`.

Tests are prompts an agent evaluates against. They catch errors and drift before chapters are finalized.

## The Standard

A reader should finish this thesis understanding adiabatic quantum optimization better than any other single source would give them.

- The writing should be clear enough to teach.
- Precise and rigorous enough that there are no errors. State what results achieve and what they do not.
- Honest, personal and reflective. The goal is new perspective: understanding reality better or building practical things.

The published paper is the foundation. The thesis explains it deeply and weaves the background into a unified whole. It proposes directions beyond the paper (legitimate future work, even if unproven) and `src/experiments/` is where we try to realize them. What succeeds gets folded back into the thesis.

## Tests

| Test | File | What it checks |
|------|------|----------------|
| Format | `check-format.md` | ASCII only, no `---` separators, LaTeX basics |
| Math | `check-math.md` | Notation consistency, correctness vs paper |
| Taste | `check-taste.md` | Prose quality, scaffolding, filler, structure |
| Review | `review.md` | Holistic peer review with weighted dimensions |

## Usage

Point Claude at content and a test file:

```
Read src/chapters/ch2.tex and run the test in src/tests/check-math.md
```

Or run all tests on a chapter:

```
Run all tests in src/tests/ against src/chapters/ch2.tex
```

## Interpreting Results

Each test outputs:
- **PASS**: No issues found
- **WARN**: Minor issues that should be reviewed
- **FAIL**: Problems that must be fixed

Agent tests include specific line references and suggested fixes.

## Adding Tests

Tests follow a standard format:

```markdown
# Test Name

## Purpose
What this test checks and why it matters.

## Criteria
Specific conditions to evaluate (numbered list).

## Procedure
How to run the test (what to read, what to compare).

## Output Format
How to report results.
```

- Run these checks before finalizing any chapter. Feed relevant test content to the LLM along with the draft section to catch errors early.
- Perform multiple passes through each chapter. Iterate till satisfied. Also, writing later chapters deepens understanding of earlier ones. Revisit as needed.
