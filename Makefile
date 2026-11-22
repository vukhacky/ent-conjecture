PYTHON ?= python3
PDFLATEX ?= pdflatex

.PHONY: all paper verify update-results figure checksums update-checksums
all: verify paper

paper:
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error ENT_proof.tex
	$(PDFLATEX) -interaction=nonstopmode -halt-on-error ENT_proof.tex

verify:
	$(PYTHON) code/run_all.py --check

update-results:
	$(PYTHON) code/run_all.py

figure:
	$(PYTHON) code/ent_make_figure.py --output-dir figures

checksums:
	$(PYTHON) code/checksums.py

update-checksums:
	$(PYTHON) code/checksums.py --write
