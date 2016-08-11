PROG=LeqFromMeet2
SUFF_INLINED=inlined
SUFF_SQUASHED=squashed
DIR_INLINED=compile-$(SUFF_INLINED)/
DIR_SQUASHED=compile-$(SUFF_INLINED)-$(SUFF_SQUASHED)/
HS=MAlonzo/Code/$(PROG).hs
AGDA=../.cabal-sandbox/bin/agda

inline-squash:
	rm -f $(PROG).agdai
	$(AGDA) --compile --compile-dir=$(DIR_SQUASHED) --ghc-dont-call-ghc --inline-proj --squash-cases $(PROG).agda

verbose:
	rm -f $(PROG).agdai
	$(AGDA) -v:treeless.opt.squash:30 --compile --compile-dir=compile-$(SUFF_INLINED)-$(SUFF_SQUASHED) --ghc-dont-call-ghc --inline-proj --squash-cases $(PROG).agda

inline:
	rm -f $(PROG).agdai
	$(AGDA) --compile --compile-dir=$(DIR_INLINED) --ghc-dont-call-ghc --inline-proj $(PROG).agda

unpatched:
	rm -f $(PROG).agdai
	$(AGDA) --compile --compile-dir=compile --ghc-dont-call-ghc $(PROG).agda

diff: inline inline-squash
	emacs --eval "(ediff-files \"$(DIR_INLINED)$(HS)\" \"$(DIR_SQUASHED)$(HS)\")" &

clean:
	rm -rf compile* *.agdai $(PROG)

