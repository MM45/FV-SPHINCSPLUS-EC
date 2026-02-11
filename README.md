# A Tight Security Proof for SPHINCS⁺, Formally Verified
This repository accompanies the paper "A Tight Security Proof for SPHINCS⁺,
Formally Verified", authored by Manuel Barbosa, François Dupressoir, Andreas
Hülsing, Matthias Meijers, and Pierre-Yves Strub. The most recent version of the
paper can be found [here](https://eprint.iacr.org/2024/910).  

This repository comprises EasyCrypt scripts primarly aimed at the formal
verification of the security of SPHINCS⁺, effectively verifying a modular
version of the proof presented in [Recovering the Tight Security Proof of
SPHINCS⁺](https://link.springer.com/chapter/10.1007/978-3-031-22972-5_1). Due to
the module approach, we are able to reuse some of the artifacts produced in [the
formal verification of XMSS](https://github.com/MM45/FV-XMSS-EC). Furthermore,
this repository contains several generic, reusable libraries (employed in the
development) that are either novel or improvements over previous libraries.

The most recent version of EasyCrypt that has been confirmed to verify the
scripts in this repository corresponds to [release
2026.02](https://github.com/EasyCrypt/easycrypt/releases/tag/r2026.02) with SMT
provers Z3 4.13.4 and Alt-Ergo 2.6.0 (as specified in `easycrypt.project`).

## Building, Running, and Testing

You can run this development either via Docker or natively (if you have the
correct EasyCrypt + solver installation).

### Prerequisites

- Docker approach:  
  - [Docker Engine](https://docs.docker.com/engine/install), installed and running.
- Native approach:  
  - [EasyCrypt (release r2026.02)](https://github.com/EasyCrypt/easycrypt/tree/r2026.02), installed and configured with the solvers listed below.
  - Alt-Ergo 2.6.
  - Z3 4.13.4.

For the native approach, the [EasyCrypt README.md for
r2026.02](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/README.md)
describes installation and solver configuration. More detailed instructions are
provided in the
[INSTALL.md](https://github.com/EasyCrypt/easycrypt/blob/r2026.02/INSTALL.md).

### Docker

Run all tests inside the Docker environment:
```shell
make docker-check
```

To explore and interact with the repository inside the container, start an interactive shell:
```shell
make docker-shell
```

This drops you into a shell inside the Docker image with the repository as the
working directory. From there you can run the same commands as in the native
approach (see below).

### Native

Run all tests:
```shell
make check
```

Beyond running the tests, this also stores test reports in the `reports/`
directory (automatically created on the first test run).

Remove EasyCrypt’s cached verification artifacts (.eco files):
```shell
make clean
```

Additionally remove the reports/ directory:
```shell
make clobber
```

### Help with Make
All of the above uses `make` and, hence, goes through the repository's
`Makefile`. To list available targets and brief descriptions:
```shell
make help
```

You can override `make` variables (see `Makefile`), for example to tweak the
setup or speed up testing by increasing parallelism. However, be aware that
changing these parameters can affect test stability (e.g., different degrees of
parallelism can trigger solver/time-out failures), so unexpected failures may
occur when deviating from the default settings.

