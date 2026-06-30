"""Compute the unit log-embedding matrix whose absolute determinant is the
regulator of a number field.

For a number field K with signature (r1, r2), the unit rank is r = r1 + r2 - 1.
The regulator is |det| of the matrix

    M[i, j] = e_{v_i} * log |sigma_{v_i}(u_j)|,

where u_1, ..., u_r are fundamental units, v_1, ..., v_{r1+r2} are the
archimedean places, and e_v = 1 at real places, 2 at complex places.  This is an
(r+1) x r matrix; deleting any one row gives a square r x r matrix whose absolute
determinant equals K.regulator() (independent of which row is dropped).

Usage (run under sage's python):

    sage -python generate_regulator_matrices.py "x^5 - x^4 - 2*x^2 + 4*x - 1"

The polynomial is given in the variable x; ^ and ** both work for exponents.
You may pass several polynomials at once.  With no polynomial argument, a
built-in set of examples is used.

Options:
    --name NAME     name of the number field generator   (default: a)
    --prec PREC     bit precision for the places          (default: 100)
    --digits DIGITS digits shown in the matrices          (default: 8)
    -h, --help      full help

Or import:  from generate_regulator_matrices import regulator_matrix
"""

import argparse
from random import randint
import sys

from sage.all import NumberField, Matrix, log, QQ, Infinity, matrix, RDF
from sage.rings.complex_mpfr import ComplexField_class


def regulator_matrix(K, prec=100, drop=-1):
    """Return (M, Msq) for the number field K.

    M    -- the full (r1+r2) x r log-embedding matrix
    Msq  -- the square r x r matrix obtained by deleting row ``drop``
            (default: the last row); abs(Msq.det()) == K.regulator().
    """
    units = K.unit_group().fundamental_units()   # u_1, ..., u_r
    r = len(units)
    places = K.places(prec=prec)                 # the r1 + r2 archimedean places

    rows = []
    for v in places:
        e = 2 if isinstance(v.codomain(), ComplexField_class) else 1
        rows.append([e * log(abs(v(u))) for u in units])

    M = Matrix(rows)                             # (r+1) x r
    keep = [i for i in range(M.nrows()) if i != (drop % M.nrows())]
    Msq = M.matrix_from_rows(keep)               # square r x r
    return M, Msq


def parse_poly(poly_str, var="x"):
    """Parse a polynomial string (e.g. "x^5 - x^4 - 2*x^2 + 4*x - 1") into a
    rational polynomial.  Accepts both ``^`` and ``**`` for exponentiation."""
    R = QQ[var]
    return R(poly_str.replace("^", "**"))


def random_irreducible_poly(degree, var="x", coeff_bound=4):
    """Return a random monic irreducible polynomial in ``QQ[var]``.

    The non-leading coefficients are chosen from
    ``[-coeff_bound, coeff_bound]`` until an irreducible polynomial of the
    requested degree is found.
    """
    R = QQ[var]
    x = R.gen()

    while True:
        coeffs = [randint(-coeff_bound, coeff_bound)
                  for _ in range(degree)]
        if coeffs[0] == 0:
            continue

        f = x ** degree + sum(coeffs[i] * x ** i for i in range(degree))
        print(f)
        if f.is_irreducible():
            return f


# ---------------------------------------------------------------------
# Triangular-matrix inverse-norm bounds (Higham, "Bounds for the Norm of
# the Inverse of a Triangular Matrix"), applied to the LU factors.
# ---------------------------------------------------------------------

def alpha_beta_upper(U):
    """alpha, beta for an upper triangular matrix U (as in Higham's post)."""
    n = U.nrows()
    diag = [abs(U[i, i]) for i in range(n)]
    alpha = min(diag)
    beta = 0
    for i in range(n):
        for j in range(i + 1, n):
            if U[i, j] != 0:
                beta = max(beta, abs(U[i, j]) / abs(U[i, i]))
    return alpha, beta


def alpha_beta_lower(L):
    """alpha, beta for a lower triangular matrix L (column/row roles swapped)."""
    n = L.nrows()
    diag = [abs(L[i, i]) for i in range(n)]
    alpha = min(diag)
    beta = 0
    for j in range(n):
        for i in range(j + 1, n):
            if L[i, j] != 0:
                beta = max(beta, abs(L[i, j]) / abs(L[j, j]))
    return alpha, beta


def norm_inv_bound(alpha, beta, n):
    """Bound (7): (beta+1)^(n-1) / alpha."""
    if alpha == 0:
        return Infinity
    return (beta + 1) ** (n - 1) / alpha


def lu_inverse_norm_bound(A, p='2'):
    """
    Compute LU factorization P*A = L*U of A (Sage convention),
    bound ||L^{-1}||_p, ||U^{-1}||_p via formula (7), and combine
    to bound ||A^{-1}||_p <= ||U^{-1}||_p * ||L^{-1}||_p
    (since P is a permutation, ||P^{-1}|| = 1 in these norms).
    """
    A = matrix(RDF, A)  # work numerically; use RR/QQ if you want exact entries
    n = A.nrows()
    if n != A.ncols():
        raise ValueError("A must be square")

    better_bound_Ainv = A.inverse().norm('frob')

    P, L, U = A.LU()   # Sage: P*A = L*U  (L unit lower triangular)

    alpha_L, beta_L = alpha_beta_lower(L)
    alpha_U, beta_U = alpha_beta_upper(U)

    bound_Linv = norm_inv_bound(alpha_L, beta_L, n)
    bound_Uinv = norm_inv_bound(alpha_U, beta_U, n)

    bound_Ainv = bound_Uinv * bound_Linv

    return {
        'P': P, 'L': L, 'U': U,
        'alpha_L': alpha_L, 'beta_L': beta_L, 'bound_Linv': bound_Linv,
        'alpha_U': alpha_U, 'beta_U': beta_U, 'bound_Uinv': bound_Uinv,
        'bound_Ainv': bound_Ainv,
        'better_bound_Ainv': better_bound_Ainv
    }


def norm2_bound_frobenius(A):
    """Cheap bound on ||A||_2 via ||A||_2 <= ||A||_F."""
    A = matrix(RDF, A)
    return A.norm('frob')


def norm2_bound_interp(A):
    """Cheap bound on ||A||_2 via ||A||_2 <= sqrt(||A||_1 * ||A||_oo)."""
    A = matrix(RDF, A)
    return (A.norm(1) * A.norm(Infinity)).sqrt()


def norm_power_n_minus_1_bounds(A):
    """
    Return (n-1)-power estimates of ||A||_2 using the two cheap bounds
    on ||A||_2 described above:

        ||A||_2 <= ||A||_F                       (Frobenius bound)
        ||A||_2 <= sqrt(||A||_1 * ||A||_oo)       (interpolation bound)

    raised to the (n-1) power, i.e. estimates of ||A||_2^(n-1).
    """
    A = matrix(RDF, A)
    n = A.nrows()
    frob_bound = norm2_bound_frobenius(A)
    interp_bound = norm2_bound_interp(A)
    return {
        'frob_bound': frob_bound,
        'interp_bound': interp_bound,
        'frob_bound_pow': frob_bound ** (n - 1),
        'interp_bound_pow': interp_bound ** (n - 1),
    }


def det_times_inv_norm_bound(A):
    """
    Bound for |det(A)| * ||A^{-1}|| using the PLU decomposition.

    Since A = P^{-1} L U (P a permutation, so |det P| = 1),
        |det(A)| = |det(L)| * |det(U)| = |det(U)|   (L unit triangular)
    and
        ||A^{-1}|| <= ||U^{-1}|| * ||L^{-1}||
    (bounded via formula (7), as in lu_inverse_norm_bound).  Hence

        |det(A)| * ||A^{-1}||  <=  |det(U)| * bound_Uinv * bound_Linv.

    Returns a dict with the bound and its constituent pieces.
    """
    A = matrix(RDF, A)
    n = A.nrows()
    if n != A.ncols():
        raise ValueError("A must be square")

    res = lu_inverse_norm_bound(A)
    U = res['U']

    det_U = U.det()          # = +/- det(A) up to the sign from P
    det_A = A.det()

    bound = abs(det_U) * res['bound_Uinv'] * res['bound_Linv']
    better_bound = abs(det_U) * res['better_bound_Ainv']

    return {
        'det_A': det_A,
        'det_U': det_U,
        'bound_Linv': res['bound_Linv'],
        'bound_Uinv': res['bound_Uinv'],
        'bound_Ainv': res['bound_Ainv'],
        'better_bound_det_times_Ainv': better_bound,
        'bound_det_times_Ainv': bound,
    }


def print_lu_bound_report(A, digits=8):
    """Pretty-print the result of lu_inverse_norm_bound(A), plus the
    extra quantities ||A||^(n-1) and the PLU-based bound on
    |det(A)| * ||A^{-1}||."""
    res = lu_inverse_norm_bound(A)
    n = A.nrows()

    def fmt(x):
        try:
            return x.n(digits=digits)
        except AttributeError:
            return x

    print("LU decomposition (P*A = L*U):")
    print("L =\n", res['L'].n(digits=digits))
    print("\nU =\n", res['U'].n(digits=digits))

    print("\n%-45s %s" % ("quantity", "value"))
    print("-" * 60)
    print("%-45s %s" % ("alpha_L = min_i |l_ii|", fmt(res['alpha_L'])))
    print("%-45s %s" % ("beta_L  = max_{j<i} |l_ij|/|l_jj|", fmt(res['beta_L'])))
    print("%-45s %s" % ("bound on ||L^{-1}||  (p=1,2,oo)", fmt(res['bound_Linv'])))
    print("-" * 60)
    print("%-45s %s" % ("alpha_U = min_i |u_ii|", fmt(res['alpha_U'])))
    print("%-45s %s" % ("beta_U  = max_{i<j} |u_ij|/|u_ii|", fmt(res['beta_U'])))
    print("%-45s %s" % ("bound on ||U^{-1}||  (p=1,2,oo)", fmt(res['bound_Uinv'])))
    print("-" * 60)
    print("%-45s %s" % ("bound on ||A^{-1}|| = ||U^-1||*||L^-1||",
                         fmt(res['bound_Ainv'])))

    Ainv = A.inverse()
    actual = {
        '1': Ainv.norm(1),
        '2': Ainv.norm(2),
        'oo': Ainv.norm(Infinity),
    }
    print("-" * 60)
    print("actual ||A^{-1}||_1  :", fmt(actual['1']))
    print("actual ||A^{-1}||_2  :", fmt(actual['2']))
    print("actual ||A^{-1}||_oo :", fmt(actual['oo']))

    # Final summary block, in the requested order:
    # 1. exact ||A||_2^(n-1)
    # 2. ||A||_F^(n-1) approximation of (1)
    # 3. interpolation approximation of (1)
    # 4. value of |det A| * ||A^{-1}||
    # 5. rough PLU-based bound for (4)
    print("-" * 60)
    pow_bounds = norm_power_n_minus_1_bounds(A)
    exact_pow = A.norm(2) ** (n - 1)
    det_res = det_times_inv_norm_bound(A)
    actual_det_times_inv = abs(det_res['det_A']) * actual['2']

    print("%-45s %s" % ("exact method 1 (n = %d)" % n,
                         fmt(exact_pow)))
    print("%-45s %s" % ("frob approx of (1)",
                         fmt(pow_bounds['frob_bound_pow'])))
    print("%-45s %s" % ("exact method 2",
                         fmt(actual_det_times_inv)))
    print("%-45s %s" % ("frob approx of (2)",
                         fmt(det_res['better_bound_det_times_Ainv'])))
    print("%-45s %s" % ("rough bound of (2)",
                         fmt(det_res['bound_det_times_Ainv'])))
    print("=" * 60)


def report(f, name="a", prec=100, digits=8):
    """Print the regulator-matrix report for the number field K = QQ[x]/(f)."""
    K = NumberField(f, name)
    print("=" * 70)
    print("poly:", f)
    print("signature (r1, r2):", K.signature(),
          "   unit rank:", sum(K.signature()) - 1)

    M, Msq = regulator_matrix(K, prec=prec)
    print("\nfull log-embedding matrix M (%d x %d):" % (M.nrows(), M.ncols()))
    print(M.n(digits=digits))
    print("\nsquare matrix (last row dropped, %d x %d):"
          % (Msq.nrows(), Msq.ncols()))
    print(Msq.n(digits=digits))

    A = Msq
    print("\n2-norm        :", A.norm(2))
    print("Frobenius norm:", A.norm('frob'))
    print("determinant   :", A.det())

    reg = A.det().abs()
    print("\n|det| of square matrix :", reg)
    print("K.regulator()          :", K.regulator())
    print("match:", abs(reg - K.regulator()) < 1e-15)
    print()

    print_lu_bound_report(A, digits=digits)


DEFAULT_DEGREES = range(2, 11)


def main(argv=None):
    parser = argparse.ArgumentParser(
        description="Compute the unit log-embedding (regulator) matrix of a "
                    "number field defined by a polynomial.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog='example:\n'
               '  sage -python generate_regulator_matrices.py '
               '"x^5 - x^4 - 2*x^2 + 4*x - 1"',
    )
    parser.add_argument(
        "poly", nargs="*",
        help="polynomial(s) in x defining the number field, e.g. "
             '"x^5 - x^4 - 2*x^2 + 4*x - 1".  If omitted, random '
             "irreducible polynomials of degrees 2 through 10 are generated.",
    )
    parser.add_argument(
        "--name", default="a",
        help="name of the number field generator (default: a)",
    )
    parser.add_argument(
        "--prec", type=int, default=100,
        help="bit precision for the archimedean places (default: 100)",
    )
    parser.add_argument(
        "--digits", type=int, default=8,
        help="number of digits to display in the matrices (default: 8)",
    )
    args = parser.parse_args(argv)

    if args.poly:
        polys = []
        for poly_str in args.poly:
            try:
                polys.append(parse_poly(poly_str))
            except (TypeError, ValueError, SyntaxError) as exc:
                print("error: could not parse polynomial %r: %s"
                      % (poly_str, exc), file=sys.stderr)
                return 1
    else:
        polys = [random_irreducible_poly(degree) for degree in DEFAULT_DEGREES]

    for f in polys:
        report(f, name=args.name, prec=args.prec, digits=args.digits)

    return 0


if __name__ == "__main__":
    sys.exit(main())
