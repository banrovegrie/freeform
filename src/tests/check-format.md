# Formatting Check

## Purpose

Catch formatting issues in `.md` and `.tex` files before they become problems. These are mechanical checks that do not require judgment.

## Criteria

### 1. ASCII Only

All characters must be in ASCII range (0-127).

**Common violations:**
- Curly quotes: U+201C, U+201D, U+2018, U+2019 -> use ASCII `"` and `'`
- Em/en dashes: U+2014, U+2013 -> use `---` or `--`
- Accented letters: e.g. e with acute (U+00E9) -> use `\'e` in LaTeX
- Math symbols outside LaTeX: multiplication (U+00D7), division (U+00F7), inequality symbols -> use `\times`, `\leq` etc.
- Greek letters: e.g. alpha (U+03B1) -> use `$\alpha$`

**Manual check:**
```bash
grep -rP '[^\x00-\x7F]' src/
```

### 2. No Horizontal Rule Separators

Markdown files should not use `---`, `***`, or `___` as section separators.

**Why:** I hate them.

**Manual check:**
```bash
grep -rn '^---$\|^***$\|^___$' src/*.md
```

**Exception:** YAML frontmatter delimiters at file start are acceptable.

### 3. Math Delimiters in Markdown

Mathematical expressions in `.md` files must be wrapped in `$...$` (inline) or `$$...$$` (display).

**Common violations:**
- `H(s) = (1-s)H_0 + sH_P` -> `$H(s) = (1-s)H_0 + sH_P$`
- `O(sqrt(N))` -> `$O(\sqrt{N})$`
- `A_1/(A_1+1)` -> `$A_1/(A_1+1)$`

**Why:** Renders properly in LaTeX-aware markdown viewers. Plain text math is ambiguous (is `H_0` a subscript or literal underscore?).

**Exception:** Simple variable names in prose context (e.g., "the parameter n") may remain undelimited.

### 4. LaTeX Basics

- Delimiter balance
- Bare `_` outside math mode -> use `\_` or `$H_0$`
- Bare `<` or `>` outside math -> use `$<$` or `\textless`
- Double spaces -> single space suffices
- Space before punctuation: `word .` -> `word.`

## Procedure

**Agent check:**

Read the file and scan for:
1. Non-ASCII bytes (report character and suggested replacement)
2. Horizontal rule lines (report line number)
3. Undelimited math expressions in markdown (report line and expression)
4. LaTeX issues (report line and specific problem)

## Output Format

```
PASS: No formatting issues

FAIL: Formatting issues found
  - file.md:42: non-ASCII curly quote " -> use "
  - file.md:87: horizontal rule --- -> use heading or remove
  - file.md:57: undelimited math "H(s) = (1-s)H_0" -> wrap in $...$
  - file.tex:103: bare underscore H_0 -> use $H_0$
  - file.tex:156: unbalanced $ delimiter
```
