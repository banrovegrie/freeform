# Task Plan: Format Compliance for Markdown Files

## Objective
Make all `.md` files in the repository compliant with `src/tests/check-format.md` standards.

## Phases

### Phase 1: Discovery
- [ ] Explore repository structure
- [ ] Identify all `.md` files
- [ ] Review check-format.md criteria in detail
- [ ] Check if check-md.md exists (user mentioned it)

### Phase 2: Analysis
- [ ] Scan all `.md` files for formatting violations
- [ ] Categorize issues by type (ASCII, horizontal rules, LaTeX)
- [ ] Document findings

### Phase 3: Implementation
- [ ] Fix non-ASCII characters
- [ ] Remove horizontal rule separators (except YAML frontmatter)
- [ ] Fix LaTeX issues (bare underscores, angle brackets, etc.)

### Phase 4: Verification
- [ ] Re-scan all files for compliance
- [ ] Document results

## Decisions Log
(To be updated as decisions are made)

## Current Status
**Phase**: Discovery
**Started**: 2026-02-04
