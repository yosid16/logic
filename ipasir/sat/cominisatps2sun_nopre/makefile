NAME=cominisatps
VERSION=2sun_nopre

SIG=$(NAME)$(VERSION)
DIR=$(NAME)-$(VERSION)
TARGET=libipasir$(SIG).a

# Always rebuild everything in the competition environment.
all: clean
	MROOT=.. make -C $(DIR)/simp libr
	g++ -DVERSION=\"$(VERSION)\" -I$(DIR) -I$(DIR)/simp -DNDEBUG -O3 -static -c ipasir$(NAME)glue.cc
	cp $(DIR)/simp/lib_release.a $(TARGET)
	ar r $(TARGET) ipasir$(NAME)glue.o

clean:
	MROOT=.. make -C $(DIR)/simp clean
	rm -f *.o *.a

.PHONY: all clean
