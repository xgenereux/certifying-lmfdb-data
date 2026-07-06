# Generate a `unique_root_near` profiling test file at a chosen decimal precision.
#
# Uses p = X^6 - X - 1, whose complex roots have BOTH nonzero real and nonzero
# imaginary part (worst case for the finishers: the Complex.mul_re/mul_im
# cross-terms do not cancel, unlike the pure-real/pure-imaginary roots of the
# LMFDB polynomial X^6-5X^4-50X^2+125).
#
# Usage:  sage scratchpad_gen_profile.sage <digits> <outfile.lean> [modname]
#
# The approximation v and the inverse-Jacobian matrix M are each printed with
# `digits` decimal places, so the decimal literals fed to the tactic have
# ~`digits` significant digits (the scaling axis).

import sys

digits   = int(sys.argv[1])
outfile  = sys.argv[2]
modname  = sys.argv[3] if len(sys.argv) > 3 else "ProfileGen"

# work with a comfortable guard band above the requested decimal precision
guard    = 40
prec     = int((digits + guard) * RR(10).log(2)) + 20   # bits

C  = ComplexField(prec)
RF = RealField(prec)
R0.<x> = PolynomialRing(QQ)

p  = x^6 - 2*x - 2
pd = p.derivative()

# pick the complex root with the largest imaginary part and nonzero real part
roots = p.roots(C, multiplicities=False)
cand  = [z for z in roots if z.imag() > RF(2)^(-prec//2) and abs(z.real()) > RF(2)^(-prec//2)]
rho   = sorted(cand, key=lambda z: -z.imag())[0]

def dec_to_QQ(s):
    """Exact rational equal to the decimal string `s`."""
    s = s.strip()
    neg = s.startswith('-')
    if neg:
        s = s[1:]
    if '.' in s:
        intp, frac = s.split('.')
    else:
        intp, frac = s, ''
    num = ZZ((intp + frac) or '0')
    q = QQ(num) / QQ(10) ** len(frac)
    return -q if neg else q

# a single formatting + its exact rational, guaranteed consistent
def approx(z):
    s = RF(z).str(digits=digits, no_sci=2)
    return s, dec_to_QQ(s)

def fmt(z):
    # used only for M's -b entry (already a rational); keep consistent formatting
    return RF(z).str(digits=digits, no_sci=2)

vr_s, vr = approx(rho.real())
vi_s, vi = approx(rho.imag())

# inverse Jacobian: 1/p'(rho) as a 2x2 real matrix !![a,-b; b,a]
inv = 1 / pd(rho)
a_s, a = approx(inv.real())
b_s, b = approx(inv.imag())
nb_s, _ = approx(-inv.imag())

# --- sanity: exact residual |M . p(v)| with v,M exact rationals -----------
Qv = QQ(vr) + QQ(vi)*I if False else None
# evaluate p at the Gaussian rational vr + vi*i exactly
def eval_gaussian(poly, xr, xi):
    re, im = QQ(0), QQ(0)
    cs = poly.list()
    for c in reversed(cs):
        re, im = re*xr - im*xi + QQ(c), re*xi + im*xr
    return re, im

pr, pim = eval_gaussian(p, vr, vi)
# M . (pr, pim):  row0 = a*pr - b*pim ; row1 = b*pr + a*pim
res0 = abs(a*pr - b*pim)
res1 = abs(b*pr + a*pim)
res  = max(res0, res1)

# choose radius r = 10^k.  v is accurate to `digits` places so res ~ 10^-digits;
# need r/10 >= res.  Start at k = -(digits-2) and lower k (exact QQ compare) until safe.
k = -(digits - 2)
def r_of(k):
    return QQ(10) ** k if k >= 0 else QQ(1) / QQ(10) ** (-k)
while res > 0 and r_of(k) / 10 < 20 * res:
    k += 1                      # r too small; make it bigger (k less negative)
r_str = "1e%d" % k
res_exp = res.numerator().ndigits() - res.denominator().ndigits() if res > 0 else 0

with open(outfile, "w") as f:
    f.write("import CertifyingLmfdbData.Polynomial.Tactic\n\n")
    p_lean = str(p).replace('x', 'X')
    f.write("/-! PROFILING: p = %s, mixed complex root, %d-digit precision. -/\n" % (p_lean, digits))
    f.write("open Polynomial\n")
    f.write("namespace %s\n\n" % modname)
    f.write("noncomputable def p : Polynomial ℚ := %s\n\n" % p_lean)
    f.write("def v : Fin 2 → ℝ := ![%s, %s]\n\n" % (vr_s, vi_s))
    f.write("def M : Matrix (Fin 2) (Fin 2) ℝ :=\n")
    f.write("  !![ %s, %s;\n" % (a_s, nb_s))
    f.write("      %s, %s ]\n\n" % (b_s, a_s))
    f.write("set_option maxHeartbeats 4000000 in\n")
    f.write("noncomputable def prof : UniqueRootNear p (toComplex v) %s := by\n" % r_str)
    f.write("  unique_root_near M\n\n")
    f.write("end %s\n" % modname)

print("wrote %s : digits=%d  r=%s  res~1e%d  degree=%d"
      % (outfile, digits, r_str, res_exp, p.degree()))
