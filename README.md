# CertiFlash: A Formal Verification Framework for Flash Translation Layers in Computational Solid-State Drives

## What is CertiFlash?

Computational solid-state drives let each tenant customize the flash translation
layer (FTL), but a modified FTL can silently break tenant isolation, data
integrity, or block ownership while still passing every functional test.

**CertiFlash** is a Rocq (Coq) framework for the mechanized verification of FTLs.
It proves that an FTL preserves a single global safety invariant over mapping,
tenant isolation, integrity, ownership, and allocation, and that the invariant
implies a refinement of an idealized block device. A new FTL design discharges five
hypotheses about its own operations rather than re-proving the global
invariant over its own state.

The device state is a 16-field record (`FTLState` in
`formal-proof/src/core/Model.v`) and the global safety property is a 27-clause
invariant (`ftl_invariant`, clauses `Inv0`..`Inv26`, in
`formal-proof/src/Invariants/Invariants.v`). Every operation is proved to
preserve that invariant, the invariant is shown to imply a refinement of an
idealized block device, all micro-operation preconditions are proved sound, the
modeled failure surfaces are shown reachable, and four FTL case studies plus
crash recovery are built on top of the framework. The development contains no
`Admitted` proofs and no user-introduced axioms.

## Citation

If you find this repo useful, please cite:

Harshita Gupta, Mayank Kabra, Rakesh Nadig, Nika Mansouri Ghiasi, Sahand
Divsalar, Fatma Nisa Bostancı, Ataberk Olgun, Konstantinos Kanellopoulos,
Jisung Park, Haiyu Mao, Abdullah Giray Yağlıkçı, Mohammad Sadrosadati, and Onur
Mutlu,
"CertiFlash: A Formal Verification Framework for Flash Translation Layers in
Computational Solid State Drives", 2026.

```bibtex
@misc{gupta2026certiflash,
  title  = {{CertiFlash: A Formal Verification Framework for Flash Translation Layers in Computational Solid State Drives}},
  author = {Gupta, Harshita and Kabra, Mayank and Nadig, Rakesh and Mansouri Ghiasi, Nika and Divsalar, Sahand and Bostanc{\i}, Fatma Nisa and Olgun, Ataberk and Kanellopoulos, Konstantinos and Park, Jisung and Mao, Haiyu and Ya{\u{g}}l{\i}k{\c{c}}{\i}, Abdullah Giray and Sadrosadati, Mohammad and Mutlu, Onur},
  year   = {2026}
}
```

## Table of Contents

- [What is CertiFlash?](#what-is-certiflash)
- [Citation](#citation)
- [What CertiFlash Proves](#what-certiflash-proves)
- [Repository Structure](#repository-structure)
- [Prerequisites](#prerequisites)
- [Quick Start (Docker)](#quick-start-docker)
- [Building and Verifying](#building-and-verifying)
- [Checking Rigor](#checking-rigor)
- [Paper-to-Code Map](#paper-to-code-map)
- [Real-System Demonstration](#real-system-demonstration)
- [Contact](#contact)
- [License](#license)

## What CertiFlash Proves

| Guarantee | Meaning |
|-----------|---------|
| **Invariant preservation** | Every one of the six FTL operations, including garbage collection and wear leveling, keeps the 27-clause global invariant true. |
| **Refinement** | The invariant implies that the FTL's host-visible behavior matches an idealized block device. |
| **Precondition soundness** | Every flash primitive and controller micro-operation is proved to run only where the invariant guarantees its precondition. |
| **Failure-surface reachability** | Each of the ten modeled failures is reached by a single unchecked command, which is also proved realizable. Separately, one concrete state satisfying every clause reaches a violation at each of the five surfaces. |
| **Reusability** | A design that keeps the invariant discharges five hypotheses through the `CUSTOM_FTL` interface instead of re-proving the 27 clauses over its own state. The certificate covers invariant preservation, read-after-write, and cross-address non-interference. |
| **Rigor** | No `Admitted` proofs, no `admit` tactics, no user-introduced axioms; `coqchk` confirms the results depend on no assumptions. |

## Repository Structure

The artifact has two independent parts.

```
formal-proof/            the mechanized Rocq development (self-contained)
  _CoqProject            build manifest (the 28 modules of the artifact)
  Makefile               verify / coqchk / clean / stats / report targets
  scripts/stats.py       line / definition / lemma counts for `make report`
  src/core/              geometry, state model, operational semantics, commands
  src/Invariants/        the 27-clause invariant and its preservation proofs
  src/framework/         composition and extension modules (read-disturb study)
  src/dftl/              DFTL and MegIS case studies
  src/dedup/             deduplication case study
  src/failure_surfaces/  modeled failure surfaces and their reachability
  src/validator/         executable invariant checker and test harness

real-system/             DaisyPlus OpenSSD demonstration (needs the board)
  docs/                  runbooks and recorded results
  firmware/              firmware patch and JTAG boot files
  scripts/               host-side demo scripts

Dockerfile               pinned Rocq/Coq 8.20.1 build + verify environment
LICENSE                  MIT license
```

`formal-proof/` needs no hardware and `real-system/` needs no Rocq; neither
depends on the other.

The build set is defined by `_CoqProject`. Anything reachable by `Require` from
those modules is compiled; nothing else is present in `formal-proof/src/`.

## Prerequisites

Either **Docker** (nothing else needed — see [Quick Start](#quick-start-docker)),
or a local install of:

- Rocq / Coq **8.20.1** (`coqc`, `coqchk`)
- `coq_makefile` (ships with Rocq/Coq)
- GNU `make`

No external Coq libraries are required; only the Coq standard library is used.

## Quick Start (Docker)

The one-command path. It pins Rocq/Coq 8.20.1, so no host installation is needed,
and the image fails to build if any proof fails.

```bash
docker build -t certiflash .    # builds AND verifies every proof (~2 min)
docker run --rm certiflash      # kernel re-check: confirms no axioms are used
```

## Building and Verifying

To build without Docker:

```bash
cd formal-proof
make verify      # build all proofs, then check for Admitted / Axiom
make coqchk      # kernel re-check: confirm the results use no axioms
```

Expected outcome: the build **exits 0** and compiles all 28 modules (~21k lines
of `.v`) in roughly 85 seconds on a recent laptop. The only warnings emitted are
benign `abstract-large-number` warnings (large `nat` literals in the validator
test harness); there are no errors. `make verify` ends with
`OK: no Admitted, no Axiom`.

Other targets: `make clean` removes build products; `make stats` and `make
report` print line / definition / lemma counts (the latter uses
`formal-proof/scripts/stats.py`). The raw invocation, if you prefer it, is `cd formal-proof && coq_makefile -f
_CoqProject -o CoqMakefile && make -f CoqMakefile -j4`.

## Checking Rigor

**No admits or axioms in the sources:**

```bash
grep -rnE "Admitted|admit\b|Axiom" formal-proof/src
```

This returns only documentation comments (files stating "no `Admitted`, no
`admit`, no `Axiom`") and the identifier `dftl_admit` (the DFTL model's
request-*admit* function in `formal-proof/src/dftl/DFTL.v`). There is no `Admitted` proof, no
`admit` tactic, and no `Axiom` declaration.

**Kernel re-check reports no axioms** (`make coqchk`, or directly):

```bash
cd formal-proof && coqchk -o -Q src "" Refinement Invariants.Preservation Invariants.MicroOpPreconditions CrashRefinement failure_surfaces.FSReachable dftl.DFTL dftl.MegIS dedup.Dedup
```

These leaf results transitively cover the whole development. The context summary
ends with `Axioms: <none>` (and no type-in-type, no unsafe fixpoints, no assumed
positivity), confirming the checked results depend on no assumptions.

## Paper-to-Code Map

| Claim | File(s) | Key result(s) |
|-------|---------|---------------|
| 16-field device state; 27-clause global invariant | `formal-proof/src/core/Model.v`, `formal-proof/src/Invariants/Invariants.v` | `FTLState`, `ftl_invariant` |
| Every step preserves the invariant | `formal-proof/src/Invariants/Preservation.v` | `step_preserves_invariant`, `exec_preserves_invariant`, `reachable_states_satisfy_invariant` |
| Refinement of an idealized block device | `formal-proof/src/Refinement.v`, `formal-proof/src/Specs.v` | `exec_simulates`, `device_refines_idealized_block_device` |
| Precondition soundness over all instructions | `formal-proof/src/Invariants/PrimitivePreconditions.v`, `formal-proof/src/Invariants/MicroOpPreconditions.v` | `precondition_sound` |
| Designer interface: discharge five hypotheses instead of re-proving the invariant | `formal-proof/src/core/CustomFTLInterface.v`, `formal-proof/src/framework/Composition.v` | `CUSTOM_FTL`, `Validator.custom_ftl_security_suite`, `STATE_EXTENSION`, `LayeredCUSTOM_FTL` |
| Failure-surface reachability | `formal-proof/src/failure_surfaces/FSReachable.v`, `formal-proof/src/failure_surfaces/FailureSurfaces.v`, `formal-proof/src/core/TraceRealizable.v` | `AS*_reachable_via_primitive`, `five_failure_surfaces_reachable`, `trace_realizableb_correct` |
| Case study: read-disturb tracking | `formal-proof/src/framework/Composition.v` | `read_disturb`, `rd_needs_refresh`, `read_disturb_preserves_contract` |
| Case study: DFTL | `formal-proof/src/dftl/DFTL.v` | `dftl_ok_write`, `dftl_ok_gc`, `dftl_ok_wear_level` |
| Case study: MegIS (in-storage scan) | `formal-proof/src/dftl/MegIS.v` | `isp_ok_write`, `isp_ok_submit_job`, `isp_scan_resolve_sound`, `unwrapped_gc_breaks_coarse_runs`, `unwrapped_wear_level_breaks_coarse_runs`, `unwrapped_write_breaks_coarse_runs`, `coarse_resync` |
| Case study: deduplication | `formal-proof/src/dedup/Dedup.v` | `ftl_implies_dedup_invariant`, `dedup_cannot_cross_tenants`, `dedup_exec_preserves_invariant` |
| Crash recovery | `formal-proof/src/Invariants/CrashRecovery.v`, `formal-proof/src/CrashRefinement.v`, `formal-proof/src/core/CrashPoints.v` | `crash_recover_preserves_CR`, `refines_with_crashes`, `crashes_preserve_reads` |

## Real-System Demonstration

`real-system/` holds the host-side scripts, firmware patch, and JTAG boot files that
reproduce the paper's **real-system attack demonstration**: each modeled failure
surface is triggered on a real DaisyPlus OpenSSD over the standard NVMe interface,
surfacing either as a cross-tenant read (compared by SHA-256 digest) or a
boot-time self-test of the violated invariant clause. These board experiments
demonstrate the **attacks** on real hardware; prevention is established by the
mechanized proof (the precondition bundles), not on the board. See
[`real-system/README.md`](real-system/README.md). The mechanized proofs above stand on
their own and need no hardware.

The board is the DaisyPlus OpenSSD platform from the OpenSSD Project, running
its reference FTL `gr3ftl`; see [`real-system/README.md`](real-system/README.md)
for the attribution and for what is and is not redistributed here.

## Contact

Harshita Gupta - guptah@ethz.ch

## License

CertiFlash is released under the MIT License. See [LICENSE](LICENSE) for details.
