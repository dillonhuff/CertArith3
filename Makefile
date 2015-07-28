CC := coqc

SRC := $(shell find ./ -type f -name '*.v')
OBJ := $(patsubst %.v, %.vo, $(SRC))

all: $(OBJ)

X86.vo: X86.v
	$(CC) $<

StkMachine.vo: StkMachine.v
	$(CC) $<

Arith.vo: Arith.v StkMachine.vo
	$(CC) $<

clean:
	find ./ -type f -name '*.vo' -delete
	find ./ -type f -name '*.glob' -delete
	find ./ -type f -name '*~' -delete
