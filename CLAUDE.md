# CLAUDE.md

## About

## Repository Structure and Access

```
.
|-- paper/                  Published work
|
|-- rough/                  Full Overleaf project for the published work
|
|-- references/             References cited in the published work (and more)
|   |-- README.md               Details on usage
|   +-- mds/                    Markdown conversions of PDFs
|
|-- citations/              Papers that cite the published work
|   |-- README.md               Details on usage
|   +-- mds/                    Markdown conversions of PDFs
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
|   |-- references/             BibTeX files
|   |-- tests/                  Alignment tests (notation consistency, etc.)
|   +-- experiments/            New ideas, explorations and rough drafts
|
```

## Writing and Styling Guidelines

All important content lives in `src/`. Two main file types exist:

### TeX Files (main thesis files)

- Make sure that we have consistent formatting and notation.
- Avoid bullet points.
- Not a lot of subsections. Chapters and sections best.
- Avoid small paragraphs.
- Good citations. Not too less, not too many.

### Markdown Files (helper files)

- No `---` separators.
- No non-ASCII characters in the codebase.
- Everything should be aligned well.

## Taste and Focus
