SHELL=/usr/local/bin/bash
FORTH=gforth
prefix = /usr/local
#read-only architecture-independent files
datadir = $(prefix)/share
forthdir = $(datadir)/gforth/site-forth
FORTHB=gforth -m 15M -e
VERSION=1.0
PACKAGE=garbage-collection-$(VERSION)
FILES = COPYING \
	Makefile \
	README \
	bench-gc.fs \
	bench-gc2.fs \
	compat \
	gc.fs \
	gc.html \
	space-vs-time.eps \
	test-gc.fs \
	test2-gc.fs \
	tester.fs

test:
	$(FORTH) test-gc.fs -e bye
	@echo This takes about 45s on Gforth on a Pentium-133
	time $(FORTH) -e 1 test2-gc.fs -e bye

test2:	
	@echo This takes about 35min on Gforth on a 600MHz 21164A
	time $(FORTH) -e 3 test2-gc.fs -e bye


bench:
	for i in 1 2 3 4 5 6; do time $(FORTHB) "$$i include bench-gc.fs bye"; done

bench2:
	for i in 5000 10000 15000 20000 25000 30000 35000 40000 45000 50000 60000 70000 80000 90000 100000 120000 140000 160000 180000 200000 250000 300000 350000 400000 500000 600000 800000 1000000 2000000 4000000 8000000 16000000; do time $(FORTH) -e $$i bench-gc2.fs -e bye; done

ansreport:
	gforth ans-report.fs -e "1000 true true" gc.fs -e "print-ans-report bye"

install:
	cp -rp gc.fs compat $(forthdir)
	@echo Please install gc.html in an appropriate directory

bibhtml:
	cd ~/tex/bibhtml;\
        bibhtml -r ~/a5/garbage-collection/gc -b ../d ~/a5/garbage-collection/gc.html;

dist:
	-rm -rf $(PACKAGE)
	mkdir $(PACKAGE)
	cp -rp $(FILES) $(PACKAGE)
	zip -r $(PACKAGE).zip $(PACKAGE)
