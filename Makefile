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

# The line counts of all .agda files in the project (the HEAD commit
# is used).

.PHONY: agda-loc
agda-loc :
	@git ls-tree --name-only -r -z HEAD | grep -z '\.agda$$' | \
          wc --files0-from=-

# The line counts of all .agda files in the project (the HEAD commit
# is used), excluding lines that start with "--" comments and lines
# that only contain whitespace.

.PHONY: agda-loc-nc
agda-loc-nc :
	@git ls-tree --name-only -r -z HEAD | grep -z '\.agda$$' | \
          xargs --null sed -e '/^\s*--.*/d' | grep -v '^\s*$$' | wc
