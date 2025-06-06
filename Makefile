all: hott std
.PHONY: all

hott:
	$(MAKE) -C hott all
	rm -f _CoqProject
	ln -s _CoqProject.hott _CoqProject
.PHONY: hott

std:
	$(MAKE) -C std all
	rm -f _CoqProject
	ln -s _CoqProject.std _CoqProject
.PHONY: std

clean:
	$(MAKE) -C hott clean
	$(MAKE) -C std clean
.PHONY: clean
