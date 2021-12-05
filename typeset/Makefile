OTT_OPTS  = -merge true -tex_show_meta false -tex_wrap false
OTT_FILES  = rules/rules.ott

MAIN = doc

RULESFILE = ott-rules.tex

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex $(RULESFILE)
	ott  $(OTT_OPTS) $(OTT_FILES) -tex_filter $(MAIN).tex $(MAIN).mng
	@pdflatex $(@:.pdf=.mng)

$(RULESFILE): $(OTT_FILES)
	ott $(OTT_OPTS) $(OTT_FILES) -o $@
	@if grep '<<no parses (' $@ >/dev/null 2>&1 && \
		[ -z "$(DONTSTOP)" ]; then \
			echo; \
			echo "***** OTT PARSE ERROR(S) *****"; \
			grep -n '<<no parses (' $@; \
			$(RM) $@; \
			exit 1; \
	fi >&2

clean_gen:
	@rm -f $(MAIN).mng $(RULESFILE) *.bbl  *.aux *.fls *.out *.synctex.gz *.log *.fdb_latexmk *.blg bundle.tar.gz

clean: clean_gen
	@rm -f $(MAIN).pdf

.PHONY: all clean clean_gen
