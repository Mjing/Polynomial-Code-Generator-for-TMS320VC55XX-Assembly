# Function Estimator
This module generates a TMS320VC55XX-Assembly code to estimate wave function
with a general lagrange polynomial. 

## Quick Demo
```sh
$ sml example.sml
```

## Generating Code
Check example.sml
Tips:
1. Use "lagrange" function to compute lagrange polynomial.
2. Supply memory-map of coefficients(as in "table" variable of example).
3. Use "evaluate" to set evaluation point of lagrange function.
4. Use "reduce" to simplify obtained expression.
5. Use "compile" to compile Symex-constant-expression into DSPASM-expression.
6. Use "PrintDSP" to compile DSPASM to TMS320VC55XX-assembly code.

## Using this Code
* It compiles code according to config, for estimating function from last n-inputs.
* It expects incoming n-points of signal starting from #signal onwards (in positive direction).
* Code generated needs to be placed in proper assembly file with all flags set and #signal handling. 