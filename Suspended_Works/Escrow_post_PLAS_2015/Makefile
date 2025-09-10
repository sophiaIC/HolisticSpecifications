MAIN = RiskAndTrust.pdf RiskAndTrustAppendix.pdf

%.pdf: %.tex $(wildcard *.tex) Case.bib abbrevs.bib
	pdflatex $*.tex
	bibtex $*
	pdflatex $*
	pdflatex $*.tex

%.dvi: %.tex $(wildcard *.tex) Case.bib abbrevs.bib
	latex $*.tex
	bibtex $*
	latex $*
	latex $*

%.ps: %.dvi
	dvips -o $@ -D600 -P pdf -t letter -Pdownload35 $<

all: $(MAIN)

view: all
	xdg-open $(MAIN)

clean:
	rm -f *.log *.aux *.dvi *.toc *.lof *.bbl *.blg *.out *.brf $(MAIN).pdf

.PHONY: all clean