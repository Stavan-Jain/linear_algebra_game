.PHONY: all
all: html

html: game_config.toml $(shell find src -not -name '*.olean' | sed 's/ /\\ /g')
	$(MAKE) clean
	make-lean-game --devmode
	touch html

.PHONY: run
run: html
	echo 'Ctrl+C to stop'
	python3 -m http.server -d html


.PHONY: clean
clean:
	rm -rf html
	rm -rf src/game/**/*.olean
