# CLAUDE.md

## About

This is to be my ([Alapan Chaudhuri](https://banrovegrie.github.io/)) master's thesis on adiabatic quantum optimization, supervised by Shantanav Chakraborty. The thesis is built on a single published paper in `paper/` ([Unstructured Adiabatic Quantum Optimization: Optimality with Limitations](https://arxiv.org/html/2411.05736v3)). The goal is to explain that work deeply, weave the necessary background into a unified whole, and propose directions beyond it. What starts as experiments may become contributions.

The thesis should be the best single source for understanding its subject. A reader who finishes should have new perspective, not just new facts.

- Clear enough to teach.
- Rigorous enough to test or build on.
- Novel enough to unify background and reveal new directions.
- Honest about what is achieved and what remains open.

Good work follows a cycle: study, think, act, reflect, iterate. Acting means writing, proving, experimenting. Reflecting means analyzing results and verifying claims. Maintain a plan that tracks what worked, what failed, and what to try next. Progress often comes from questioning earlier decisions and understanding why something was or was not done. Build taste and intuition through rigor and strong trial and error, not through shortcuts. To do something new: one must know the foundations intimately, yet be brave enough to take risks. Keep pushing much further in ideas and execution.

## Repository Structure and Access

For use in `src/` (main thesis work):

1. `paper/` and `rough/` are the most important because they are about the published work.
2. `references/` and `citations/` are important because they are about the references and citations used in the published work. The published work has only one good paper citing it which is the only one there (in `citations/`). We can make use of the bibliographies present in either for our thesis.
3. `taste/` is about the style to base thesis on. Mostly we will distill this information here itself under the `Taste and Style` section.
4. `src/experiments/` for new ideas, explorations, and rough drafts before they mature into chapters.
5. `src/tests/` for alignment tests including notation consistency checks, taste comparisons, and math verification prompts.

For direct comparison and unsupervised feedback we have `taste/zeeshan_ms_thesis.md` and `taste/dewolf_phd_thesis.md` as barebone baselines. We aim to write much much better than them with new work introduced as well.


```
.
|-- paper/                  Published work
|
|-- rough/                  Full Overleaf project for the published work
|
|-- references/             References cited in the paper (usable for thesis)
|   |-- README.md               Index of references
|   +-- mds/                    Markdown files of the references
|
|-- citations/              Papers that cite the paper (usable for thesis)
|   |-- README.md               Index of citing papers
|   +-- *.tex                   LaTeX files of the citations
|
|-- taste/                  Style reference work
|   |-- README.md               Index organized by author with style notes
|   +-- *.md                    Works and papers in markdown format
|
|-- src/                    Main thesis work
|   |-- main.tex                Main TeX file
|   |-- Makefile                Makefile for building the PDF
|   |-- references.bib          BibTeX references
|   |-- chapters/               Chapter TeX files
|   |-- frontmatter/            Title, abstract, acknowledgements, etc.
|   |-- images/                 Images used in thesis
|   |-- tests/                  Alignment tests (notation consistency, etc.)
|   +-- experiments/            New ideas, explorations and rough drafts
|
```

## Guidelines

All important content lives in `src/`.

### Writing

- Simple and coherent enough to understand (as simple as possible but not simpler for non-triviality or orthogonality has its place) yet rigorous enough to be able to experiment with the ideas.
- Make sure that we have consistent formatting and notation.
- Avoid bullet points.
- Not a lot of subsections. Chapters and sections best.
- Avoid small paragraphs.
- Good citations. Not too less, not too many.
- Avoid grandesque statements. Keep sentences small and direct.
- No empty sentences. LLMs produce filler sentences that mean nothing. Every sentence must carry information.
- Background check previous chapters before introducing definitions. Common repeated terms: hermitian, unitary, spectral gap. Do not re-define.
- Generate a broad chapter index first. Use it as skeleton. Plan the story flow before filling content. Rearranging pieces later is hard.
- LLMs struggle with technical depth. Feed relevant source content (paper, references) to produce substantive paragraphs.
- Notation and math hallucination is easy to miss. Import math directly from the published paper where possible. Shantanav catches math errors immediately.
- Structure is fluid. Plan extensively before committing. Use `tests/` for notation consistency checks and more.

### Formatting

- Avoid `---` separators in `.md` files.
- No non-ASCII characters in the codebase.
- Everything should be aligned well.
- All math in `.tex` or `.md` should follow right LaTeX conventions.

### Taste and Style

Good technical writing makes the reader feel that each idea arrives exactly when needed. Before any definition appears, the reader already wants it. Before any theorem is stated, the reader understands what gap it fills. This is not achieved by announcing "we now motivate X" but by genuinely building the intellectual tension that makes X necessary.

The best thesis writing combines three voices. The Philosopher asks why this matters, what is at stake, what question the reader already cares about. The Engineer states precisely what is achieved and at what cost, with explicit bounds and dependencies. The Teacher guides the reader through unfamiliar territory with patience, using concrete examples that recur throughout. Use all three: philosophical framing in introductions, engineering precision in results, pedagogical care everywhere.

A common failure mode is to name these qualities rather than embody them. Writing "from a philosophical standpoint" or "to provide intuition" signals awareness of good practice while missing the substance. The goal is invisible craft: the reader experiences clarity without noticing technique.

When writing with AI assistance, there is a specific danger. LLMs are trained on text that often fills space rather than carrying meaning. The output will tend toward vague generalities, hedged claims, and filler sentences unless actively counteracted. Every sentence must earn its place. If a sentence can be removed without information loss, remove it.

The thesis concerns adiabatic quantum optimization. Use consistent notation throughout. Import mathematical statements directly from the published paper where possible. Notation and mathematical details are where LLMs fail most invisibly. Shantanav will catch errors here.

For elaboration on specific authors and detailed patterns, see `taste/README.md`.

### Testing

See `src/tests/README.md` for alignment and correctness tests. Run before finalizing chapters. Iterate till satisfied.
