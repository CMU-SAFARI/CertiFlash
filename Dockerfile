# Reproducible build environment for the CertiFlash artifact.
#
# Pins Coq / Rocq 8.20.1 so the proof check reproduces from a clean image with
# no host Coq installation. The build itself runs `make verify`, so the image
# fails to build if any proof fails or any Admitted / Axiom is present.
#
#   docker build -t certiflash .          # builds AND verifies all proofs
#   docker run --rm certiflash            # kernel re-check: confirms no axioms
#
FROM coqorg/coq:8.20.1

SHELL ["/bin/bash", "--login", "-c"]
WORKDIR /home/coq/certiflash
COPY --chown=coq:coq . .

# The Rocq development lives in formal-proof/; real-system/ holds the board demo
# and needs no build.
WORKDIR /home/coq/certiflash/formal-proof

# Verify during image build. `docker build` is red if verification fails.
RUN eval $(opam env) && make clean && make verify

# Default run: kernel re-check that the trusted results depend on no axioms.
CMD eval $(opam env) && make coqchk
