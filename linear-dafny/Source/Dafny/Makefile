# ###############################################################################
# The frame files are no longer in this directory. They must be downloaded
# from http://boogiepartners.codeplex.com/. Update the FRAME_DIR variable to
# point to whatever directory you install that into.
# ###############################################################################
FRAME_DIR = ..\..\third_party\Coco\src

# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
all: Parser.cs

PARSER_PREREQS=$(FRAME_DIR)\Scanner.frame $(FRAME_DIR)\Parser.frame
ifeq ($(shell uname),Linux)
# Linux needs forward slashes. Maybe those are okay on windows too?
E_PARSER_PREREQS=$(subst \,/,$(PARSER_PREREQS))
# Linux needs to invoke the parser via mono.
E_COCO=mono $(subst \,/,$(COCO))
E_FRAME_DIR=$(subst \,/,$(FRAME_DIR))
else
# Windows
E_PARSER_PREREQS=$(PARSER_PREREQS)
E_COCO=$(COCO)
E_FRAME_DIR=$(FRAME_DIR)
endif
Parser.cs: $(E_PARSER_PREREQS) Dafny.atg
	$(E_COCO) Dafny.atg -namespace Microsoft.Dafny -frames $(E_FRAME_DIR)

clean:
	if exist Scanner.cs del Scanner.cs
	if exist Scanner.cs.old del Scanner.cs.old
	if exist Parser.cs del Parser.cs
	if exist Parser.cs.old del Parser.cs.old
