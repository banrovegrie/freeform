# Formatting Check

## Purpose

Catch formatting issues in `.md` and `.tex` files before they become problems. These are mechanical checks that do not require judgment.

## Criteria

### 1. ASCII Only

All characters must be in ASCII range (0-127).

**Common violations:**
- Curly quotes: U+201C, U+201D, U+2018, U+2019 -> use ASCII `"` and `'`
- Em/en dashes: U+2014, U+2013 -> restructure sentence (see rule 3)
- Accented letters: e.g. e with acute (U+00E9) -> use `\'e` in LaTeX
- Math symbols outside LaTeX: multiplication (U+00D7), division (U+00F7), inequality symbols -> use `\times`, `\leq` etc.
- Greek letters: e.g. alpha (U+03B1) -> use `$\alpha$`

**Manual check:**
```bash
grep -rP '[^\x00-\x7F]' src/
```

### 2. No Horizontal Rule Separators

Markdown files should not use `---`, `***`, or `___` alone on a line as section separators (horizontal rules).

**Why:** I hate them.

**Manual check:**
```bash
grep -rn '^---$\|^***$\|^___$' src/*.md
```

**Exceptions:**
- YAML frontmatter delimiters at file start are acceptable.

### 3. No Em Dashes or En Dashes

No em dashes or en dashes, whether Unicode (U+2014, U+2013) or ASCII (`---`, `--` used as punctuation).

Single hyphens are fine: compound words (`NP-hard`, `well-known`), list markers, CLI flags, file paths.

**Common violations:**
- `the bottleneck --- not information` -> restructure: `the bottleneck is not information`
- `results -- stated with bounds` -> restructure: `results, stated with bounds`
- `spine --- a few questions` -> restructure: `spine: a few questions`

**Manual check:**
```bash
# Unicode em/en dashes
grep -rP '[\x{2013}\x{2014}]' src/
# ASCII em dashes (three consecutive hyphens not in code blocks or horizontal rules)
grep -rn ' --- ' src/
# ASCII en dashes (double hyphen used as punctuation, not in code/comments)
grep -rn ' -- ' src/
```

**Why:** They break reading rhythm and look sloppy. Restructure the sentence instead.

### 4. Math Delimiters in Markdown

Mathematical expressions in `.md` files must be wrapped in `$...$` (inline) or `$$...$$` (display).

**Common violations:**
- `H(s) = (1-s)H_0 + sH_P` -> `$H(s) = (1-s)H_0 + sH_P$`
- `O(sqrt(N))` -> `$O(\sqrt{N})$`
- `A_1/(A_1+1)` -> `$A_1/(A_1+1)$`

**Why:** Renders properly in LaTeX-aware markdown viewers. Plain text math is ambiguous (is `H_0` a subscript or literal underscore?).

**Exceptions:**
- Simple variable names in prose context (e.g., "the parameter n") may remain undelimited.
- Notation reference tables (e.g., the tables in `check-math.md`) where columns describe symbol names and their LaTeX forms are exempt. The table structure already makes the mathematical intent clear.

### 5. LaTeX Basics

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
3. Em/en dashes, Unicode or ASCII (report line and suggest restructure)
4. Undelimited math expressions in markdown (report line and expression)
5. LaTeX issues (report line and specific problem)

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
