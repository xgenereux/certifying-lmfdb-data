# Emit `unique_root_near` certificates (root approximation + inverse-Jacobian
# matrix A) for every root of a given polynomial, as valid Lean code.
#
# For a root rho of p, the zero-finder Jacobian is multiplication by p'(rho),
# i.e. the real 2x2 matrix  !![re, -im; im, re]  with (re,im) = p'(rho).
# The certificate matrix A is its inverse, i.e. the complex number 1/p'(rho)
# written as a 2x2 real matrix  !![a, -b; b, a]  with a+bi = 1/p'(rho).
# Real roots collapse to the diagonal  !![1/p', 0; 0, 1/p'].
#
# Usage: edit `p`, `prec` and `radius` below, then run
#     sage scratchpad_root_certificates.sage

prec   = 200                       # working precision in bits
radius = "1e-57"                   # sup-norm radius r for the certificate
digits = int(prec * RR(2).log(10))     # decimal digits to print

C = ComplexField(prec)
R0.<x> = PolynomialRing(QQ)

# ---- the polynomial ----------------------------------------------------------
p = x^6 - 5*x^4 - 50*x^2 + 125

# -----------------------------------------------------------------------------
pd = p.derivative()

def fmt(z):
    """Format a real number as a Lean decimal literal at the chosen precision."""
    return RealField(prec)(z).str(digits=digits, no_sci=2)

def is_real(z, tol):
    return abs(z.imag()) < tol

roots = p.roots(C, multiplicities=False)
tol   = C(2) ^ (-prec // 2)

# Real roots (by value), then one representative of each conjugate pair (im > 0).
real_roots    = sorted([z for z in roots if is_real(z, tol)], key=lambda z: z.real())
complex_roots = sorted([z for z in roots if z.imag() > tol],  key=lambda z: z.real())

def emit(name, rho, real):
    """Print the Lean `def`s for the root vector and inverse-Jacobian matrix."""
    inv = 1 / pd(rho)                     # 1/p'(rho) as a complex number
    a, b = inv.real(), inv.imag()
    re, im = rho.real(), rho.imag()

    print("def %sroot : Fin 2 → ℝ := ![%s, %s]" % (name, fmt(re), fmt(im)))
    if real:
        # b ~ 0; keep the exact zeros so the matrix is diagonal.
        print("def %sA_mat : Matrix (Fin 2) (Fin 2) ℝ :=" % name)
        print("  !![ %s, 0;" % fmt(a))
        print("      0, %s ]" % fmt(a))
    else:
        print("def %sA_mat : Matrix (Fin 2) (Fin 2) ℝ :=" % name)
        print("  !![ %s, %s;" % (fmt(a), fmt(-b)))
        print("      %s, %s ]" % (fmt(b), fmt(a)))
    print("")
    print("example : UniqueRootNear myPoly (toComplex %sroot) %s := by" % (name, radius))
    print("  unique_root_near %sA_mat" % name)
    print("")

print("-- Certificates for roots of  p = %s" % p)
print("-- precision = %d bits (~%d digits), radius r = %s\n" % (prec, digits, radius))

for i, rho in enumerate(real_roots, 1):
    emit("r%d" % i, rho, real=True)

for i, rho in enumerate(complex_roots, 1):
    emit("c%d" % i, rho, real=False)
