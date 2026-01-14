This directory contains a TLA+ specification of the Angelfish protocol as well as a Makefile allowing to check them with the TLC model-checker.

## Makefile usage

Most targets expect `TLA_SPEC` to point at a `.tla` file. The default config file is inferred as `$(basename TLA_SPEC).cfg`, but you can override it via `TLC_CFG`.

Common commands:

- `make tla2tools.jar` (or any other target) downloads the TLC jar if it is missing.
- `make trans TLA_SPEC=Angelfish.tla` runs the PlusCal translator (`pcal.trans -nocfg`). The Angelfish specification uses the PlusCal language, which must first be transpiled to TLA+ before model-checking. This should have been done be default in this repo.
- `make sany TLA_SPEC=Angelfish.tla` runs the SANY syntax checker.
- `make run-tlc TLA_SPEC=TLCAngelfish1.tla` runs the TLC model checker on the `TLCAngelfish1.tla` specification. This specification imports the main `Angelfish.tla` specification and fixes a small system size and small execution bounds.
- `make block-dag-test` runs TLC for `BlockDagTest.tla` using `BlockDagTest.cfg`. This runs some basic tests of the definitions in `BlockDag.tla`.
- `make Angelfish.pdf` builds a PDF from `Angelfish.tla` via `tla2tex` and `pdflatex`.

You can override TLC resources per run, for example:

```
make run-tlc TLA_SPEC=Angelfish.tla TLC_HEAP=4G TLC_WORKERS=4
```
