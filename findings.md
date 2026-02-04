# Findings: Format Compliance Analysis

## Format Check Criteria (from check-format.md)

### 1. ASCII Only
- All characters must be in ASCII range (0-127)
- Common violations: curly quotes, em/en dashes, accented letters, math symbols, Greek letters

### 2. No Horizontal Rule Separators
- No `---`, `***`, or `___` as section separators
- Exception: YAML frontmatter delimiters at file start

### 3. LaTeX Basics
- Delimiter balance
- No bare `_` outside math mode
- No bare `<` or `>` outside math
- No double spaces
- No space before punctuation

## Files to Check
(To be populated after discovery)

## Violations Found
(To be populated after analysis)
