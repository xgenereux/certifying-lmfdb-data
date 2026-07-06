# Emit `unique_root_near` certificates (root approximation + inverse-Jacobian
# matrix A) for every root of a given polynomial.
#
# For a root rho of p, the zero-finder Jacobian is multiplication by p'(rho),
# i.e. the real 2x2 matrix  !![re, -im; im, re]  with (re,im) = p'(rho).
# The certificate matrix A is its inverse, i.e. the complex number 1/p'(rho)
# written as a 2x2 real matrix  !![a, -b; b, a]  with a+bi = 1/p'(rho).
# Real roots collapse to the diagonal  !![1/p', 0; 0, 1/p'].
#
# At high precision the certificate numbers are tens of thousands of digits, so
# rather than inline `![…]`/`!![…]` literals we write each root's vector and
# matrix to a separate plain-text file (the format the `load_vec`/`load_mat`
# elaborators of `LoadCert.lean` read) and emit Lean that loads them — exactly
# like the 100k/1M-digit test files.
#
# Usage: edit `p`, `prec` and `radius` below, then run
#     sage scratchpad_root_certificates.sage

prec   = 200                       # working precision in bits
radius = "1e-57"                   # sup-norm radius r for the certificate
digits = int(prec * RR(2).log(10))     # decimal digits to print

# directory the .txt certificate files are written to, relative to the repo root
# (`sage` is expected to be run from there); also used verbatim in the emitted
# `load_vec`/`load_mat` path strings.
cert_dir = "CertifyingLmfdbData/Polynomial/Tests"

C = ComplexField(prec)
R0.<x> = PolynomialRing(QQ)

# ---- the polynomial ----------------------------------------------------------
p = x^6 - 5*x^4 - 50*x^2 + 125

# -----------------------------------------------------------------------------
pd = p.derivative()

def fmt(z):
    """Format a real number as a decimal literal at the chosen precision."""
    return RealField(prec)(z).str(digits=digits, no_sci=2)

def is_real(z, tol):
    return abs(z.imag()) < tol

roots = p.roots(C, multiplicities=False)
tol   = C(2) ^ (-prec // 2)

# Real roots (by value), then one representative of each conjugate pair (im > 0).
real_roots    = sorted([z for z in roots if is_real(z, tol)], key=lambda z: z.real())
complex_roots = sorted([z for z in roots if z.imag() > tol],  key=lambda z: z.real())

def emit(name, rho, real):
    """Write the root vector and inverse-Jacobian matrix to `.txt` files and
    print the Lean `def`s that load them plus the certificate `example`."""
    inv = 1 / pd(rho)                     # 1/p'(rho) as a complex number
    a, b = inv.real(), inv.imag()
    re, im = rho.real(), rho.imag()

    v_path = "%s/cert_%s_v.txt" % (cert_dir, name)
    m_path = "%s/cert_%s_m.txt" % (cert_dir, name)

    # vector file:  re, im
    with open(v_path, "w") as f:
        f.write("%s, %s" % (fmt(re), fmt(im)))

    # matrix file:  a, -b; b, a  (diagonal a,0;0,a for a real root, where b ~ 0)
    with open(m_path, "w") as f:
        if real:
            f.write("%s, 0;\n0, %s" % (fmt(a), fmt(a)))
        else:
            f.write("%s, %s;\n%s, %s" % (fmt(a), fmt(-b), fmt(b), fmt(a)))

    print("noncomputable def %sroot : Fin 2 → ℝ :=" % name)
    print("  load_vec \"%s\"" % v_path)
    print("noncomputable def %sA_mat : Matrix (Fin 2) (Fin 2) ℝ :=" % name)
    print("  load_mat \"%s\"" % m_path)
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
