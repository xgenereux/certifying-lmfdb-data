# this extension is AI generated and needs to be sanity checked

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
    }


def print_lu_bound_report(A, digits=8):
    """Pretty-print the result of lu_inverse_norm_bound(A)."""
    res = lu_inverse_norm_bound(A)

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


DEFAULT_POLYS = [
    "x^5 - x^4 - 2*x^2 + 4*x - 1",
    "x^10 - 2*x^9 - x^8 + 4*x^7 - 3*x^6 - 4*x^5 + 7*x^4 + 4*x^3 "
        "- 5*x^2 - x + 1",
    "x^8 - x^7 - 2*x^6 + x^5 + x^3 + 2*x^2 - 1",
]


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
             '"x^5 - x^4 - 2*x^2 + 4*x - 1".  If omitted, a built-in set of '
             "example polynomials is used.",
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

    poly_strs = args.poly if args.poly else DEFAULT_POLYS

    for poly_str in poly_strs:
        try:
            f = parse_poly(poly_str)
        except (TypeError, ValueError, SyntaxError) as exc:
            print("error: could not parse polynomial %r: %s" % (poly_str, exc),
                  file=sys.stderr)
            return 1
        report(f, name=args.name, prec=args.prec, digits=args.digits)

    return 0


if __name__ == "__main__":
    sys.exit(main())