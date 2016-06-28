PROG=InlineTest
SUFF=inlined
HS=MAlonzo/Code/$(PROG).hs

diff: patched unpatched
	@echo "***********************DIFF***********************"
	diff compile/$(HS) compile-$(SUFF)/$(HS)

patched:
	agda --compile --compile-dir=compile-$(SUFF) --ghc-dont-call-ghc --inline-proj $(PROG).agda

unpatched:
	agda --compile --compile-dir=compile --ghc-dont-call-ghc $(PROG).agda

clean:
	rm -rf compile* *.agdai $(PROG)

