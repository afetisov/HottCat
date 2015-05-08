VFILES=Pushforwards.v Misc.v TFunctors.v Option.v
VOFILES=$(VFILES:.v=.vo)
GLOBFILES=$(VFILES:.v=.glob)

all: $(VOFILES) $(GLOBFILES)

$(VOFILES): $(VFILES)
	hoqc.lnk Pushforwards.v
	hoqc.lnk TFunctors.v
	hoqc.lnk Misc.v
	hoqc.lnk Option.v

clean:
	-rm -f $(VOFILES) $(GLOBFILES)