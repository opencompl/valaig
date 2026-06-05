# Valaig

Valaig is a framework for efficient And-Inverter Graph (AIG) manipulation and reasoning in Lean,
with a verified checker for the [certifaiger](https://github.com/Froleyks/certifaiger) model
checking certificate format.

# Building Valaig

This requires Lean 4, easily installed through the [elan toolchain](https://github.com/leanprover/elan).
To build all Valaig tools:

```bash
lake build
```

# Checking a certificate

NOTE: The certificate checker is not yet fully verified, and likely contains bugs. Currently, only
certificates without latches are supported, but this covers IC3 proofs. You can generate and check
a certificate with [rIC3](https://github.com/gipsyh/rIC3) as follows:

```bash
ric3 check --cert certificate.aig problem.aig ic3
lake exe valaigcert problem.aig certificate.aig
```
