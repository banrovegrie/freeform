# CLAUDE.md

## About

This is to be my ([Alapan Chaudhuri](https://banrovegrie.github.io/)) master's thesis on adiabatic quantum optimization, supervised by Shantanav Chakraborty. The thesis is built on a single published paper in `paper/` ([Unstructured Adiabatic Quantum Optimization: Optimality with Limitations](https://arxiv.org/html/2411.05736v3)). The goal is to explain that work deeply, weave the necessary background into a unified whole, and propose directions beyond it. What starts as experiments may become contributions.

The thesis should be the single best source for understanding its subject. A reader who finishes should have new perspective, not just new facts.

- Clear enough to teach.
- Rigorous enough to test or build on.
- Novel enough to unify background and reveal new directions.
- Honest about what is achieved and what remains open.

## Repository Structure and Access

For use in `src/` (main thesis work):

1. `paper/` and `rough/` are the most important because they are about the published work.
2. `references/` and `citations/` are important because they are about the references and citations used in the published work. The published work has only one good paper citing it which is the only one there (in `citations/`). We can make use of the bibliographies present in either for our thesis.
3. `taste/` is about the style to base thesis on. Mostly we will distill this information here itself under the `Taste and Style` section.
4. `src/experiments/` for new ideas, explorations, and rough drafts before they mature into chapters.
5. `src/tests/` for alignment tests including notation consistency checks, taste comparisons, and math verification prompts.
6. For direct comparison and unsupervised feedback we have `taste/zeeshan_ms_thesis.md` and `taste/dewolf_phd_thesis.md` as barebone baselines that we would want to beat.


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
|-- run/                    Temporary run details (planning, logs, etc.)
|
```

## Guidelines

All important content lives in `src/`.

### Writing

- Simple and coherent enough to understand (as simple as possible but not simpler for non-triviality or orthogonality has its place) yet rigorous enough to be able to experiment with the ideas.
- The thesis must exceed the paper in exposition depth, motivation and accessibility. Every concept the paper introduces tersely should get a fuller treatment: why it's needed, what it controls, how it connects to what came before.
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
- Notation and math hallucination is easy to miss. Import math directly from the published paper where possible. Any human expert would catch such math errors immediately.
- Structure is fluid. Plan extensively before committing. Use `tests/` for notation consistency checks and more.

### Formatting

- Avoid `---` separators in `.md` files.
- No non-ASCII characters in the codebase.
- Everything should be aligned well.
- All math in `.tex` or `.md` should follow right LaTeX conventions and delimiters.
- Avoid using too much of `---` in text and only if absolutely necessary.

### Taste and Style

Before writing a chapter, identify its spine: the few questions that determine order. Write one page naming the tension, the main results with hypotheses, one sentence per chapter. Build a skeleton: each chapter's question, the definitions it needs, the theorems, the lemmas.

Before introducing any concept, build the tension that makes it necessary. The reader should want the definition before it appears, understand what gap a theorem fills before it is stated. Only introduce a definition when current language is insufficient. Use it immediately.

Exposition needs two passes. First explain plainly: what the statement means, what the parameters control, what the theorem enables. Then state and prove. State proof strategy upfront. Decompose into lemmas matching logical moves, not algebraic accidents. State results with explicit bounds, clear dependencies, honest limitations. Use concrete examples that recur and accumulate meaning.

Do not signal technique. Never write "to provide intuition" or "from a philosophical standpoint". Just provide the intuition, just make the philosophical point. Do not announce what you are doing. Do it.

Revise in passes: structure, clarity, precision, style. Write out of order, for example, introduction last. Test each section: what can the reader do after reading this that they could not do before? If the answer is nothing, delete it.

LLMs are trained on text that fills space. Output tends toward vague generalities, hedged claims, and filler. Every sentence must carry information. If a sentence can be removed without information loss, remove it. Use theorem skeletons and claims paired with proofs. Demand lifted statements from sources, not invention. Require explicit assumptions and named failure modes. Import mathematical statements directly from the published paper where possible. Notation and mathematical details are where LLMs fail most invisibly. A human expert would catch errors here. You may outsource production. You cannot outsource judgment.

For detailed analysis of specific authors and their patterns, see `taste/README.md`.

### Testing

See `src/tests/` for alignment and correctness tests. Run before finalizing chapters. Iterate till satisfied.
