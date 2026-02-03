LATEX_FLAGS=-pdflatex

## Source Latex files
TEX_MAIN = main.tex
TEX_NOTES = notes.tex

# Generate PDF files
PDF_MAIN = main.pdf
PDF_NOTES = notes.pdf

IMAGES := $(wildcard images/*.jpg images/*.pdf images/*.png)

${PDF_MAIN}: ${TEX_MAIN} ${IMAGES}
	latexmk ${LATEX_FLAGS} ${TEX_MAIN}

${PDF_NOTES}: ${TEX_NOTES} ${IMAGES}
	latexmk ${LATEX_FLAGS} ${TEX_NOTES}

all: ${PDF_MAIN} ${PDF_NOTES}

main: ${PDF_MAIN}

notes: ${PDF_NOTES}

clean:
	rm -rf ${DIFF_PREV_PDF} *.bbl; latexmk -C
