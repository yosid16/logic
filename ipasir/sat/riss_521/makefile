#-----------------------------------------------------------------------#
#- GLOBAL DEFS ---------------------------------------------------------#
#-----------------------------------------------------------------------#

# Keep this as generic as possible.
NAME=riss
VERSION=521


SIG=$(NAME)_$(VERSION)
DIR=$(NAME)_$(VERSION)
TARGET=libipasir$(SIG).a


#-----------------------------------------------------------------------#
#- REQUIRED TOP RULES --------------------------------------------------#
#-----------------------------------------------------------------------#

all: $(TARGET)

clean:
	rm -f  *.a
	rm -rf $(DIR)


#-----------------------------------------------------------------------#
#- INVISIBLE INTERNAL SUB RULES ----------------------------------------#
#-----------------------------------------------------------------------#

libipasir$(SIG).a: .FORCE
	@#
	@# extract library
	@#
	rm -rf $(DIR)
	tar xvf $(DIR).tar.gz
	@#
	@# configure and build library
	@#
	mkdir -p $(DIR)/build
	cd $(DIR)/build; cmake -DQUIET=ON -DCMAKE_BUILD_TYPE=Release -DSTATIC_BINARIES=ON ..
	cd $(DIR)/build; make riss-coprocessor-lib-static
	@#
	@# move library here
	@#
	mv $(DIR)/build/lib/libriss-coprocessor.a $(TARGET)

.FORCE:
.PHONY: all clean
