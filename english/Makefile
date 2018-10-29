all:
	lualatex -draftmode -shell-escape -interaction=nonstopmode main.tex
	lualatex -draftmode -shell-escape -interaction=nonstopmode main.tex
	makeglossaries main
	lualatex -shell-escape -interaction=nonstopmode main.tex

clean:
	rm -rf *.aux *.glg *.glo *.gls *.ist *.listing
	rm -rf *.pdf *.log *.out *.thm *.toc _minted-main
