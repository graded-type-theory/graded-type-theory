## HTML Output ############################################################

htmldir=html
agda=agda
main=Everything.agda

.PHONY: html
html :
	$(agda) --html --html-dir=$(htmldir) $(main)

## Type Check Code ########################################################

.PHONY: check
check :
	$(agda) $(main)

## Lines of Code ##########################################################

# Agda files in this project

agdalocfiles=$(shell find . \( \( -name '*.agda' \) ! -name '.*' \) )

# Sum all agda files

.PHONY: agda-loc
agda-loc :
	@wc $(agdalocfiles)

# Delete comments (sed) and empty lines (grep .) first

.PHONY: agda-loc-nc
agda-loc-nc :
	@sed -e '/--.*/d' $(agdalocfiles) | grep . | wc

# EOF
