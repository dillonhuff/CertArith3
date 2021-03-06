CC := coqc

SRC := $(shell find ./ -type f -name '*.v')
OBJ := $(patsubst %.v, %.vo, $(SRC))

all: $(OBJ)

X86.vo: X86.v
	$(CC) $<

RSMachine.vo: RSMachine.v
	$(CC) $<

StkMachine.vo: StkMachine.v
	$(CC) $<

Arith.vo: Arith.v
	$(CC) $<

ArithToStk.vo: ArithToStk.v Arith.vo StkMachine.vo
	$(CC) $<

StkToRS.vo: StkToRS.v StkMachine.vo RSMachine.vo
	$(CC) $<

clean:
	find ./ -type f -name '*.vo' -delete
	find ./ -type f -name '*.glob' -delete
	find ./ -type f -name '*~' -delete
