PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: paper verify figure all
all: verify paper

paper:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error ENT_proof.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error ENT_proof.tex

verify:
	$(PYTHON) code/run_all.py

figure:
	$(PYTHON) code/ent_make_figure.py --output-dir figures
