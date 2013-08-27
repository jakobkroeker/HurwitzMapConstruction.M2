
MACAULAY2_SHARE_PATH=~/.Macaulay2/local/share/Macaulay2
RFSDIR=rationalFunctionSearch



.PHONY: all install

all:


install:
	cp ./padicLift.m2  $(MACAULAY2_SHARE_PATH)
	cp ./rationalFunctionSearch.m2 $(MACAULAY2_SHARE_PATH)/
	cp ./rationalFunctionSearch/rfsObjects.m2 $(MACAULAY2_SHARE_PATH)/$(RFSDIR)/
	cp ./rationalFunctionSearch/rfsIO.m2 $(MACAULAY2_SHARE_PATH)/$(RFSDIR)/
	cp ./rationalFunctionSearch/rfsPrepareLift.m2 $(MACAULAY2_SHARE_PATH)/$(RFSDIR)/
	cp ./rationalFunctionSearch/rfsTests.m2 $(MACAULAY2_SHARE_PATH)/$(RFSDIR)/
