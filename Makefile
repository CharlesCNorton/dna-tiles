ROCQC := rocq compile
OPTS := -R . DNATiles

VFILES := Core.v Results.v Advanced.v
VOFILES := $(VFILES:.v=.vo)

all: $(VOFILES)

Core.vo: Core.v
	$(ROCQC) $(OPTS) Core.v

Results.vo: Results.v Core.vo
	$(ROCQC) $(OPTS) Results.v

Advanced.vo: Advanced.v Core.vo Results.vo
	$(ROCQC) $(OPTS) Advanced.v

clean:
	rm -f *.vo *.vok *.vos *.glob *.aux .*.aux

.PHONY: all clean
