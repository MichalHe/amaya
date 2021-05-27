
CO=analysis




all: $(CO).html

%.html: %.ipynb
	jupyter-nbconvert --to html --no-input --no-prompt --execute $<

%.ipynb: %.md
	jupytext --output $@ $<
