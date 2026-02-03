# CLAUDE.md

## About

[TODO]

## Repository Structure and Access

For use in `src/` (main thesis work):
1. `paper/` and `rough/` are the most important because they are about the published work.
2. `references/` and `citations/` are important because they are about the references and citations used in the published work. The published work has only one great paper citing it which is the only one there. We can use the bibliography of that to use in our thesis.
3. `taste/` and `template/` are about the style (think: taste) and template (think: format), respectively, to base thesis on. Mostly we will distill this information here itself under the `Taste and Style` section.

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
|-- template/               LaTeX template to follow
|   |-- main.tex                Main TeX file
|   |-- Makefile                Makefile for building the PDF
|   |-- chapters/               Chapter TeX files
|   |-- frontmatter/            Title, abstract, acknowledgements, etc.
|   |-- images/                 Images used
|   +-- references/             BibTeX files
|
|-- src/                    Main thesis work
|   |-- main.tex                Main TeX file
|   |-- Makefile                Makefile for building the PDF
|   |-- chapters/               Chapter TeX files
|   |-- frontmatter/            Title, abstract, acknowledgements, etc.
|   |-- images/                 Images used in entire src
|   |-- references/             References for the thesis (not paper) as BibTeX files
|   |-- tests/                  Alignment tests (notation consistency, etc.)
|   +-- experiments/            New ideas, explorations and rough drafts
|
```

## Guidelines

All important content lives in `src/`. Two main file types exist:

### Writing

- Simple and coherent enough to understand (as simple as possible but not simpler for non-triviality or orthogonality has its place) yet rigorous enough to be able to experiment with the ideas.
- Make sure that we have consistent formatting and notation.
- Avoid bullet points.
- Not a lot of subsections. Chapters and sections best.
- Avoid small paragraphs.
- Good citations. Not too less, not too many.

### Formatting

- Avoid `---` separators in `.md` files.
- No non-ASCII characters in the codebase.
- Everything should be aligned well.

## Taste and Style

[TODO]
