# Log matrix of the fundamental units fundU1-4 for the field
#   K = Q[x]/(x^6 - 5 x^4 - 50 x^2 + 125),  signature (r1,r2) = (4,1).
# Places: the 4 real embeddings + 1 complex place; unit rank = 4+1-1 = 4.

prec = 200
R = RealField(prec)
C = ComplexField(prec)

R0.<x> = PolynomialRing(QQ)
p = x^6 - 5*x^4 - 50*x^2 + 125

# The six roots, matching AllRoots.lean (4 real, 1 conjugate complex pair).
# Take the roots straight from the defining polynomial at high precision.
roots = p.roots(C, multiplicities=False)

# Sort: real roots first (by value), then one representative of each complex pair (im > 0).
real_roots    = sorted([z for z in roots if abs(z.imag()) < R(1e-30)], key=lambda z: z.real())
complex_roots = sorted([z for z in roots if z.imag() > R(1e-30)],     key=lambda z: z.real())

# One approximation per place: 4 real + 1 complex.  (m_i = 1 for real, 2 for complex.)
places = [(z, 1) for z in real_roots] + [(z, 2) for z in complex_roots]

# The fundamental units as polynomials in a root (from AllRoots.lean).
fundU1 = (1/25)*x^4 - 2
fundU2 = (1/25)*x^4 - 1
fundU3 = (1/25)*x^5 - (2/25)*x^4 - 2*x + 3
fundU4 = (1/25)*x^5 - (1/5)*x^2 - 2*x - 2
units = [fundU1, fundU2, fundU3, fundU4]

# L[i][j] = m_i * log |u_j(rho_i)|
L = Matrix(R, len(places), len(units),
           lambda i, j: places[i][1] * log(abs(units[j](places[i][0]))))

print("Roots (places):")
for z, m in places:
    print("  m=%d  rho = %s" % (m, z))

print("\nLog matrix L (rows = places, cols = units u1..u4):")
for i in range(L.nrows()):
    print("  " + "  ".join("% .15f" % L[i][j] for j in range(L.ncols())))

# Regulator = |det| of any r-subset of rows (drop one place). Sanity check.
r = len(units)
print("\nRow sums (should be ~0, product formula):")
for j in range(L.ncols()):
    print("  u%d: % .3e" % (j+1, sum(L[i][j] for i in range(L.nrows()))))

print("\nRegulator (drop last row): %.15f" % abs(L[:r, :].det()))
