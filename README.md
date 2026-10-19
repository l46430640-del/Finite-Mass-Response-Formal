# Finite Mass Response

Lean 4 proofs of finite, nonzero mass response at a Cauchy horizon for the
spherically symmetric Einstein-Maxwell system with a neutral massless scalar
field and positive cosmological constant.

## Mathematical scope

The results concern characteristic initial data at the critical relation
`innerRate = (1 - 1 / p) * outerRate`, with finite `p >= 4`. A fixed positive
outgoing tail satisfies exponential upper and lower bounds. Moving the common
initial corner sufficiently far along that tail gives a single domain on which
the nonlinear developments of a sequence of incoming packets all exist.

The incoming data converge in `L^p`, while their terminal mass differences
converge to a finite positive function. The proofs also establish the exact
blueshift rate, an all-time `L^2` radiation comparison, a cumulative mass law,
mass quantile asymptotics, and the response to finite signed packet families.
Each development admits a local spherical weak extension. The local causal
horizon is identified relative to the original characteristic initial surfaces
in the constructed ambient neighborhood. These are characteristic interior
results; a global exterior or collapse construction is outside their scope.

The three principal existence theorems are proved, with their full hypotheses
and conclusions given in the following files. All names below belong to the
`CauchyHorizon.Background` namespace.

| Theorem | Source |
| --- | --- |
| `exists_late_packet_mass_response` | [PacketMass.lean](CauchyHorizon/Characteristic/PacketMass.lean) |
| `exists_late_finite_packet_mass_response` | [FinitePacketMass.lean](CauchyHorizon/Characteristic/FinitePacketMass.lean) |
| `exists_late_pair_packet_mass_response` | [PairPacketMass.lean](CauchyHorizon/Characteristic/PairPacketMass.lean) |

`CauchyHorizon.lean` imports all 463 proof modules. `Tests.lean` and the 55
modules under `Tests/` check theorem interfaces and consequences.

## Build and verify

Install [elan](https://github.com/leanprover/elan) and
[PowerShell 7](https://github.com/PowerShell/PowerShell), then run:

```sh
git clone https://github.com/l46430640-del/Finite-Mass-Response-Formal.git
cd Finite-Mass-Response-Formal
git checkout v0.1.0
lake exe cache get
pwsh -NoProfile -File ./verify.ps1
```

The toolchain is Lean `v4.33.1`. Mathlib is pinned to
`0df444a360eaa60ab8c11dca51a86af692955474`; `lake-manifest.json` pins its
transitive dependencies. The cache command downloads compiled public
dependencies. Project proofs and tests are built from source.

The verification script uses two Lean threads, checks that every proof module
is imported, builds all default targets, and runs `Audit.lean` afresh. A
successful run reports:

```text
AUDIT_OK declarations=4123 theorems=3705
VERIFIED productionModules=463
```

The audit checks the transitive axiom dependencies of every declaration in
the `CauchyHorizon` namespace. Only Lean's `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Project axioms, unsafe declarations, proof
placeholders, native proof shortcuts, and kernel-check bypasses are rejected.
The GitHub Actions workflow repeats this verification from public dependencies.

## License

Copyright 2026 l46430640-del.

Licensed under [Apache-2.0](LICENSE). Dependencies retain their respective
licenses and are obtained separately through Lake.
