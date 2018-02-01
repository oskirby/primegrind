CFLAGS += -pthread

all: primegrind
clean:
	rm -rf primegrind

primegrind: primegrind.c
