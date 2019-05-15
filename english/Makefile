FILE=main.tex

all:
	lualatex -draftmode -shell-escape ${FILE}
	lualatex -draftmode -shell-escape ${FILE}
	makeglossaries main
	lualatex -shell-escape ${FILE}

clean:
	rm -rf *.aux *.glg *.glo *.gls *.ist *.listing
	rm -rf *.pdf *.log *.out *.thm *.toc _minted-main
