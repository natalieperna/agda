PROG=LeqFromMeet2
SUFF=inlined
HS=MAlonzo/Code/$(PROG).hs
AGDA=../.cabal-sandbox/bin/agda

diff: patched unpatched
	@echo "***********************DIFF***********************"
	diff compile/$(HS) compile-$(SUFF)/$(HS)

patched:
	$(AGDA) --compile --compile-dir=compile-$(SUFF) --ghc-dont-call-ghc --inline-proj $(PROG).agda

unpatched:
	$(AGDA) --compile --compile-dir=compile --ghc-dont-call-ghc $(PROG).agda

clean:
	rm -rf compile* *.agdai $(PROG)

