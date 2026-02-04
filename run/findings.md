# Findings: Format Compliance Audit

## Repository Structure

Total markdown files: 109 (excluding .lake/ external dependencies)
- `src/experiments/`: 39 files (project experiments)
- `references/mds/`: 52 files (reference papers converted to markdown)
- `taste/`: 20 files (style reference documents)
- Root/other: README.md, CLAUDE.md, src/tests/, src/lean/, citations/

## Format Requirements (from check-format.md)

### 1. ASCII Only
All characters must be in ASCII range (0-127).
- Curly quotes -> ASCII quotes
- Em/en dashes -> `---` or `--`
- Greek letters -> `$\alpha$` etc.
- Math symbols outside LaTeX -> proper LaTeX

### 2. No Horizontal Rule Separators
No `---`, `***`, or `___` as section separators (YAML frontmatter ok).

### 3. Math Delimiters in Markdown
All math must be in `$...$` or `$$...$$`.

### 4. LaTeX Basics
- Balanced delimiters
- No bare `_` outside math
- No bare `<` or `>` outside math
- Single spaces, no space before punctuation

## Files to Check

### High Priority (src/experiments/)
- `04_separation_theorem/notes/gap_uninformed_theorem.md`: 461 non-ASCII bytes
- `04_separation_theorem/notes/theoretical_separation.md`: 423 non-ASCII bytes

### Medium Priority (references/mds/)
Top offenders by non-ASCII byte count:
- `arthurthesis.md`: 4497 bytes
- `aaronson2011bosonsampling.md`: 1573 bytes
- `chakraborty2024implementing.md`: 999 bytes
- `albash2018adiabatic.md`: 968 bytes
- Many more with 300-600 bytes

### Lower Priority (taste/)
These are reference documents with significant non-ASCII content:
- `2504.02385.md`: 14099 bytes
- `2510.06851.md`: 13795 bytes
- `2411.05736.md`: 10818 bytes
- Most files have 1000+ non-ASCII bytes

## Issues Found

### Non-ASCII Characters
78 files contain non-ASCII characters (excluding run/ and .lake/).

Common patterns expected:
- Smart/curly quotes: `"` `"` `'` `'`
- Em-dash: `—` (U+2014)
- En-dash: `–` (U+2013)
- Greek letters outside math: `α`, `β`, `Δ`, etc.
- Mathematical symbols: `×`, `≤`, `≥`, `→`, etc.

### Horizontal Rules
Initial check: PASS (no violations found)

### Math Delimiters
To be checked per-file during remediation.

### LaTeX Issues
To be checked per-file during remediation.
