CURRENT=paper

WGETDVANHORNBIB=curl -o dvanhorn.bib "http://www.citeulike.org/bibtex/user/dvanhorn?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"
WGETIANJOHNSONBIB=wget -O ianjohnson.bib \
	          "http://www.citeulike.org/bibtex/user/ianjohnson?fieldmap=posted-at:date-added&do_username_prefix=1&key_type=4&fieldmap=url:x-url&fieldmap=doi:x-doi&fieldmap=address:x-address&fieldmap=isbn:x-isbn&fieldmap=issn:x-issn&fieldmap=month:x-month&fieldmap=comment:comment&fieldmap=booktitle:booktitle&fieldmap=abstract:x-abstract&fieldmap=pages:pages&volume:volume"

default: $(CURRENT).pdf


# Crude word-counting:
.PHONY: wc
wc:
	@wc -w abstract.tex
	@wc -w content.tex

# Open
open:
	xdg-open $(CURRENT).pdf

edit:
	emacs $(CURRENT).tex &

# Check style:
proof:
	echo "weasel words: "
	sh bin/weasel *.tex
	echo
	echo "passive voice: "
	sh bin/passive *.tex
	echo
	echo "duplicates: "
	perl bin/dups *.tex


# Forcibly refresh bibliography:
refresh: getbib

# Forcibly refresh bibliogaphy:
getbib:
	$(WGETDVANHORNBIB)
	$(WGETIANJOHNSONBIB)
	cat dvanhorn.bib ianjohnson.bib local.bib > bibliography.bib
	-bibclean bibliography.bib > bibliography.bib.clean
	-mv bibliography.bib.clean bibliography.bib

all:
	pdflatex $(CURRENT)
	bibtex $(CURRENT)
	pdflatex $(CURRENT)
	pdflatex $(CURRENT)

# Run bibtex:
bibtex:
	bibtex $(CURRENT)


%.dvi: %.tex *.tex
	latex $(basename $@)

%.pdf: *.tex
	pdflatex $(CURRENT)

# %.pdf: %.dvi
#	dvipdfm -o $(basename $@).pdf $(basename $@).dvi


# Clean out net-fetched files:
flush: clean
	rm -f ianjohnson.bib

# Clean out local intermediate files:
clean:
	rm -f paper.{dvi,ps,pdf,log,toc,blg,bbl,aux,rel} *.log *~


