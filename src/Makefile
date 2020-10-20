export AGDA ?= agda

SRC=$(shell find . -name '*.agda')
RES=$(patsubst %.agda,%.agdai,$(SRC))

all: $(RES)

%.agdai: %.agda
	$(AGDA) $<

clean:
	rm *.agdai Unknown/*.agdai
