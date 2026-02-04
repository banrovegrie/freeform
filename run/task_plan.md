# Task Plan: Format Compliance for Markdown Files

## Objective
Make all `.md` files in the repository compliant with `src/tests/check-format.md` standards.

## Phases

### Phase 1: Discovery
- [x] Study repository structure
- [x] Read `src/tests/check-format.md` requirements
- [x] Read `src/tests/check-math.md` for notation standards
- [x] Identify all `.md` files in the repository
- [x] Categorize files by location and severity

### Phase 2: Audit
- [x] Check for non-ASCII characters - **78 files affected**
- [x] Check for horizontal rule separators - **PASS, none found**
- [ ] Check for undelimited math expressions
- [ ] Check for LaTeX issues (bare underscores, unbalanced delimiters)

### Phase 3: Remediation
- [ ] Fix non-ASCII in `src/experiments/` (priority: these are project files)
- [ ] Fix non-ASCII in `references/mds/` (52 files)
- [ ] Fix non-ASCII in `taste/` (20 files)
- [ ] Fix undelimited math expressions
- [ ] Fix LaTeX issues

### Phase 4: Verification
- [ ] Re-run all format checks
- [ ] Confirm all files pass

## Status
**Current Phase**: Phase 2 - Audit / Phase 3 - Remediation (starting)

## Scope Decision

### Files to Fix
1. **src/experiments/**: All files - these are project content
2. **references/mds/**: All files - used for thesis references
3. **taste/**: All files - style reference documents
4. **Root files**: CLAUDE.md, README.md, citations/README.md, src/tests/*, src/lean/README.md

### Files to Skip
- `.lake/`: External Lean dependencies (not project files)
- `run/`: Planning files (temporary)

## Decisions Log
| Decision | Rationale | Date |
|----------|-----------|------|
| Planning files in `run/` folder | User preference for keeping planning separate from main content | 2026-02-04 |
| Fix all project .md files | check-format.md applies to entire codebase per CLAUDE.md guidelines | 2026-02-04 |
| Start with src/experiments/ | Highest priority - actual thesis work | 2026-02-04 |
