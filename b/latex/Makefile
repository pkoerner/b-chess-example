DOT=/usr/local/bin/dot
SFDP=/usr/local/bin/sfdp
prob_visualise_board.pdf: prob_visualise_board.tex
	pdflatex prob_visualise_board.tex
prob_visualise_board.tex: prob_visualise_board_raw.tex ../chess.mch
	time probcli ../chess.mch -latex prob_visualise_board_raw.tex prob_visualise_board.tex -p path_to_dot $(DOT) -init
