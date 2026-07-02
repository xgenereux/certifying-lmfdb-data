#!/usr/bin/env sage
r"""Generate the prime-norm data and numeric constants for
`CertifyingLmfdbData/ResidueLowerBoundDegSix.lean` (LMFDB field 6.4.19208000.1,
defining polynomial f = x^6 - 5x^4 - 50x^2 + 125, X = 1000, M = 9).

Run with:  sage generate_residue_data.sage

What it does:
  1. Builds K = Q[x]/(f) and lists the norms of all prime ideals of O_K of norm < X.
     `K.primes_of_bounded_norm` factors each rational prime in O_K directly, including
     the ramified prime 5 (it contributes a single prime of norm 125).
  2. Prints the Lean list literals `ratPrimes1000` and `nfPrimesNorms1000`.
  3. Computes reference values of the four bSumFin sums, the denominator, fK, the
     Belabas-Friedman error bound, and exp(c - b), and asserts that the rational
     constants used in the Lean file are correct with comfortable margins.
"""

X = 1000
M = 9
RR = RealField(200)                 # 200 bits of working precision

# ---------------------------------------------------------------------------
# 1. The field and its prime-ideal norms
# ---------------------------------------------------------------------------
R.<x> = QQ[]
f = x^6 - 5*x^4 - 50*x^2 + 125
K.<a> = NumberField(f)

assert K.discriminant() == -19208000    # confirms f defines LMFDB 6.4.19208000.1

rat_primes = list(primes(X))
assert len(rat_primes) == 168

# All prime ideals of O_K of norm < X, with multiplicity (one norm per prime ideal).
nf_norms = sorted(P.norm() for P in K.primes_of_bounded_norm(X - 1))
assert len(nf_norms) == 169


def lean_list(name, n, entries):
    return f"def {name} : Fin {n} → ℕ :=\n  ![" + ", ".join(map(str, entries)) + "]"


print(lean_list("ratPrimes1000", 168, rat_primes))
print()
print(lean_list("nfPrimesNorms1000", 169, nf_norms))
print()

# ---------------------------------------------------------------------------
# 2. Reference values
# ---------------------------------------------------------------------------
def bTerm(Xv, q, m):
    if q^m < Xv:
        return sqrt(Xv) * log(Xv) / (m * q^m) - log(RR(q)) / sqrt(RR(q))^m
    return RR(0)


def bSumFin(Xv, qs):
    return sum(bTerm(Xv, q, m) for q in qs for m in range(1, M + 1))


A = bSumFin(RR(X), nf_norms)
B = bSumFin(RR(X), rat_primes)
C = bSumFin(RR(X) / 9, nf_norms)
D = bSumFin(RR(X) / 9, rat_primes)
denom = 2 * sqrt(RR(X)) * log(RR(3 * X))
fK = 3 * ((A - B) - (C - D)) / denom

disc_abs = RR(19208000)
n_deg = 6
b_true = RR('2.324') * log(disc_abs) / (sqrt(RR(X)) * log(RR(3 * X))) * (
    (1 + RR('3.88') / log(RR(X) / 9)) * (1 + 2 / sqrt(log(disc_abs)))^2
    + RR('4.26') * (n_deg - 1) / (sqrt(RR(X)) * log(disc_abs)))

print(f"A (K,  X=1000)   = {A}")
print(f"B (Q,  X=1000)   = {B}")
print(f"C (K,  X=1000/9) = {C}")
print(f"D (Q,  X=1000/9) = {D}")
print(f"denominator      = {denom}")
print(f"fK               = {fK}")
print(f"error bound      = {b_true}")

# ---------------------------------------------------------------------------
# 3. The rational constants used in the Lean file, with margin assertions
# ---------------------------------------------------------------------------
A_lo = RR(2726476467) / 10^7    # bSumFin_nf_1000_lower
B_hi = RR(4876942414) / 10^7    # bSumFin_rat_1000_upper
C_hi = RR(394024845) / 10^7     # bSumFin_nf_ninth_upper
D_lo = RR(872115488) / 10^7     # bSumFin_rat_ninth_lower
d_lo = RR(5063671459) / 10^7    # denom_lower
c = RR(-9909) / 10^4            # fK_lower / hc
b = RR(6281) / 10^4             # errBound_upper / hb
z = RR(198) / 10^3              # final residue lower bound


def check(label, ok, margin):
    print(f"  {label}: margin = {margin}")
    assert ok, label


print("margin checks:")
check("A_lo <= A", A_lo <= A, A - A_lo)
check("B <= B_hi", B <= B_hi, B_hi - B)
check("C <= C_hi", C <= C_hi, C_hi - C)
check("D_lo <= D", D_lo <= D, D - D_lo)
check("d_lo <= denom", d_lo <= denom, denom - d_lo)

# hc:  c <= fK.  Proof route in Lean: c*denom <= c*d_lo <= N_lo <= N = fK*denom.
N_lo = 3 * ((A_lo - B_hi) - (C_hi - D_lo))
check("c*d_lo <= N_lo", c * d_lo <= N_lo, N_lo - c * d_lo)
check("c <= fK", c <= fK, fK - c)

# hb:  error bound <= b
check("b_true <= b", b_true <= b, b - b_true)

# hz:  z <= exp(c - b)
check("z <= exp(c-b)", z <= exp(c - b), exp(c - b) - z)
