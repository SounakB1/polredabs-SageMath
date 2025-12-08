from sage.all import *

def discrete_log(a):
    return dilog(a)

def is_prim_pol(f, p):
    """
    is pol irreducible and primitive?

    TESTS:

        sage: R.<x> = PolynomialRing(GF(7))
        
        sage: f = x^3 + 3*x + 2  # primitive
        sage: is_prim_pol(f, 7) # True

        sage: f = x^2 + 3 # reducible
        sage: is_prim_pol(f, 7) # False

        sage: f = x^2 + 1 # irreducible but not primitive
        sage: is_prim_pol(f, 7) # False
    """
    Fp = GF(p)
    m = f.degree()

    if not f.is_irreducible():
        return False

    K.<a> = GF(p**m, modulus=f)

    return a.multiplicative_order() == p**m - 1

def unram_pol_jr(m, p): # way too slow? O(p^m) runtime
    """
    TESTS:
        sage: pol = unram_pol_jr(3, 5)
        sage: pol # x^3 + 4 * x + 2

        sage: pol = unram_pol_jr(8, 13)
        sage: pol # takes too long to run

    """
    # returns primitive polynomial of degree m over F_p
    RZ = PolynomialRing(ZZ, 'x')
    x = RZ.gen()
    pol = x**m

    while True:
        j = 0
        s = 1
        # increment coefficients
        while pol[j] == (p-1)*s:
            pol -= s*(p-1)*x**j
            s = -s
            j += 1
        pol += s*x**j

        # reduce mod p
        R = PolynomialRing(GF(p), 'x')
        xp = R.gen()
        pol_mod_p = R([c % p for c in pol.list()])

        # check primitivity from prev function
        if is_prim_pol(pol_mod_p, p):
            return pol_mod_p

    return pol_mod_p

def conway_or_jr_polynomial(K, n):
    """
    Return a Conway polynomial of degree n.

    EXAMPLES:
        sage: K = GF(7)
        sage: pol = conway_or_jr_polynomial(K, 3)
        sage: pol # x^3 + 6*x^2 + 4

        sage: K2 = GF(11)
        sage: pol = conway_or_jr_polynomial(K,4)
        sage: pol # x^4 + 8*x^2 + 10*x + 2
    """
    p = K.characteristic()
    F = GF(p**n, name='a')
    return F.modulus().change_ring(K)

def residue_factor(phi, p):
    """
    EXAMPLES:

        sage: R.<x> = PolynomialRing(GF(7))
        sage: phi = (x^2 + 3*x + 5)^2
        sage: nu = residue_factor(phi,7)
        sage: phi, nu # (x^4 + 6*x^3 + 5*x^2 + 2*x + 4, x^2 + 3*x + 5)

        sage: R.<x> = PolynomialRing(GF(11))
        sage: phi = x^3 + 4*x + 6 # not a power of irreducible polynomial
        sage: nu = residue_factor(phi, 11)
        sage: phi, nu # (x^3 + 4*x + 6, 'Phi is not a power of an irreducible polynomial.')

        sage: R.<x> = PolynomialRing(GF(3))
        sage: phi = (x^2 + x + 1)^2 # x^2 + x + 1 = (x+2)^2 is power of irreducible polynomial
        sage: nu = residue_factor(phi, 3)
        sage: phi, nu # (x^4 + 2*x^3 + 2*x + 1, x + 2)

        sage: R.<x> = PolynomialRing(GF(3))
        sage: phi = (x^2 + 2)^2 # x^2 + 2 is reducible and not power of deg 1 poly
        sage: nu = residue_factor(phi, 3)
        sage: phi, nu # (x^4 + x^2 + 1, 'Phi is not a power of an irreducible polynomial.')

        sage: R.<x> = PolynomialRing(GF(13))
        sage: phi = 13*x^5 + 26*x + 13 # 0 poly
        sage: nu = residue_factor(phi, 13)
        sage: phi, nu # (0, 'The inputted polynomial is 0.')
    """
    RZ = phi.parent()
    Fp = GF(p)

    Rp.<x> = PolynomialRing(Fp)
    coeffs_mod_p = [c % p for c in phi.list()]
    Rphi = Rp(coeffs_mod_p)

    if Rphi.is_zero():
        return "The inputted polynomial is 0."

    facs = Rphi.factor()
    if len(facs) != 1:
        return "Phi is not a power of an irreducible polynomial."

    nu = facs[0][0]  # irreducible factor mod p

    lifted = RZ([ZZ(c) for c in nu.list()])

    return lifted


def is_eisenstein_form(phi): # * fix function must include nu, not checking if eisenstein but rather eisenstein form
    """
    sage vers of Magma's IsEisensteinForm

    EXAMPLES:

        sage: K = Qp(5)
        sage: R.<x> = K[]
        sage: phi = x^4 + x^3 + x^2 + x + 1
        sage: is_eisenstein_form(phi, 5) # should be yes

        # from polredabs.m

        sage: K = Qp(3)
        sage: R.<X> = K[]
        sage: phi = x^6 + 246*x^4 + 84*x + 30
        sage: is_eisenstein_form(phi, 3)
    """
    R = phi.parent()
    K = R.base_ring()

    if not hasattr(K, "prime"):
        return False

    p = K.prime()  

    nu = residue_factor(phi, p)
    if nu == 0:
        return False

    if nu.leading_coefficient() != 1:
        return False

    # expansion of phi in powers of nu
    g = phi
    nuexp = []
    while True:
        q, r = g.quo_rem(nu)
        nuexp.append(r)
        if q == 0:
            break
        g = q

    coeffs0 = nuexp[0].coefficients()
    vals0 = [valuation(a, p) for a in coeffs0 if a != 0]
    if len(vals0) == 0 or min(vals0) != 1:
        return False
        
    for i in range(1, len(nuexp)):
        for a in nuexp[i].coefficients():
            if a != 0 and valuation(a, p) < 1:
                return False

    return True

def eisenstein_form(L, K):
    """
    A generating polynomial phi in K[x] of L in Eisenstein form along with
    the polynomial nu generating the unramified subextensions of L/K and gamma with phi(gamma) = 0.

    EXAMPLES:
        sage: K = Qp(5, prec = 5)
        sage: R.<x> = K[]
        sage: f = x^2-5
        sage: L.<a> = K.extension(f)
        sage: phi, nu, gamma = eisenstein_form(L, K)
        sage: phi, nu, gamma, phi(gamma)
    """
    R = PolynomialRing(L, 't')
    t = R.gen()
    pi = L.uniformizer()

    if L.inertia_degree() == L.degree():
        n = L.inertia_degree()
        nu = Polynomial(K, conway_or_jr_polynomial(PrimeRing(K), n))
        phi = L.defining_polynomial()
        alpha = (R(nu - pi)).roots(multiplicities=False)[0]
        return nu, nu, alpha

    elif L.ramification_index() == L.degree():
        phi = L.defining_polynomial()
        Rk = PolynomialRing(K, 'x')
        x = Rk.gen()
        return phi, x, L.gen()

    else:
        n = L.inertia_degree()  
        nu = Polynomial(K, conway_or_jr_polynomial(PrimeRing(K), n))
        gamma = (R(nu - pi)).roots(multiplicities=False)[0]
        phi = gamma.minpoly(K)
        return phi, nu, gamma

def EisensteinForm_poly(f, K):
    """
    Given f irreducible, return a polynomial g in Eisenstein form such that K[x]/(g)
    is isomorphic to the extension generated by f.
    """
    L = K

    RL = L.residue_field()
    f = f.change_ring(L)
    if is_eisenstein_form(f):
        ext = L.extension(f, 'alpha')
        return f

    if f.change_ring(RL).is_irreducible():
        U = L.extension(f, 'beta', names=('beta',))
        return eisenstein_form(U, K)

    fac = f.change_ring(RL).factor()
    residue_deg = fac[0][0].degree()

    poly_for_U = conway_or_jr_polynomial(RL, residue_deg)
    U = L.extension(poly_for_U, 'u')

    fac2 = f.change_ring(U).factor()
    Ls = [U.extension(g[0], 'zeta') for g in fac2]
    return eisenstein_form(Ls[0], K)

def EisensteinForm_simple(f):
    K = f.base_ring()
    return EisensteinForm_poly(f, K)

def residual_polynomial_of_component_abs(phi, nu, alpha, m):
    """
   The residual polynomial of the segment of the ramfication polygon of phi of slope -m and the Hasse Herbrand function of phi at m. 
   alpha is a root of phi and nu(alpha) a uniformizing element in the extensions generated by alpha.}

    EXAMPLES:

        sage: p = 3
        sage: prec = 20
        sage: K = Qp(p, prec)
        sage: R.<x> = K[]

        sage: phi = x^2 - 3 # irreducible and eisenstein
        sage: alpha_field = K.extension(phi, names='x')
        sage: alpha = alpha_field.gen()

        sage: nu = x
        sage: m = 1

        sage: Sm, cont = residual_polynomial_of_component_abs(phi, nu, alpha, m)
        sage: print(Sm, ",", cont)
    """
    L = alpha.parent()
    LX = L['X']
    X = LX.gen()

    rho = (phi.change_ring(L)).subs(X + alpha)

    nualpha = nu(alpha)

    RL = L.residue_field()
    RLz = RL['z']
    z = RLz.gen()

    rhom = rho.subs(X=nualpha**m * X)

    # Min valuation
    coeff_vals = [c.valuation() for c in rhom.list() if c != 0]
    cont = min(coeff_vals)

    rdpc = rhom / (nualpha**cont)

    coeffs = [c.residue() for c in rdpc.list()]
    Sm = sum(coeffs[i] * z**i for i in range(len(coeffs)))

    return RLz(Sm), cont

def RamificationPoly(phi, alpha, nu=None):
    """
    Return the ramification polynomial of phi at alpha.
    """

    if nu is None:
        R = parent(phi)
        x = R.gen()
        nu = x
    
    n = phi.degree()
    nualpha = nu(alpha)

    # formula: rho(x) = phi(alpha + x*nualpha) / nualpha^n
    R.<x> = PolynomialRing(alpha.parent())
    rho = phi(alpha + x*nualpha) / (nualpha**n)

    rp = rho # modified later

    return rp, rho

def LowerSlopes(f):
    np = f.newton_polygon()
    return [slope for slope, _ in np.lower_slopes()]

def LowerVertices(f):
    np = f.newton_polygon()
    return np.lower_vertices()

def ResidualPolynomialOfComponentAbs(phi, nu, alpha, m):
    """
    The residual polynomial of the segment of the ramfication polygon of phi of slope -m and the
    Hasse Herbrand function of phi at m. alpha is a root of phi and nu(alpha) a uniformizing element 
    in the extensions generated by alpha.

    EXAMPLES:
        sage: p = 3
        sage: prec = 20
        sage: K = Qp(p, prec)
        sage: R.<x> = K[]
        sage: phi = x^2 - 3
        sage: L.<a> = K.extension(phi)
        sage: nu = x
        sage: m = 1
        sage: Sm, cont = ResidualPolynomialOfComponentAbs(phi, nu, a, m)
        sage: print(Sm, " ", cont)
    """
    # Ramification Poly
    rp, rho = RamificationPoly(phi, alpha)
    LX = rho.parent()
    L = LX.base_ring()
    X = LX.gen()

    nualpha = nu(alpha)
    rhom = rho.subs(X=nualpha**m * X)

    # Min valuation
    coeffs = rhom.list()
    coeff_vals = [c.valuation() for c in coeffs if c != 0]
    cont = min(coeff_vals)

    rdpc = rhom / (nualpha**cont)

    # Coefs go to res field
    RL = L.residue_field()
    RLz = RL['z']
    z = RLz.gen()
    coeffs_res = [c.residue() for c in rdpc.list()]

    # Res polynomial
    Sm = sum(coeffs_res[i] * z**i for i in range(len(coeffs_res)))

    return RLz(Sm), cont

def ResidualPolynomial(phi, nu, alpha):
    """
    The residual polynomials of the segments of the ramfication polygon of phi.
alpha is a root of phi and nu(alpha) a uniformizing element in the extensions generated by alpha

    EXAMPLES:

    sage: K = Qp(5, prec=60)
    sage: R.<x> = K[]
    sage: phi = x^3 - 5
    sage: L.<alpha> = K.extension(phi)
    sage: nu = x

    sage: residuals = ResidualPolynomial(phi, nu, alpha)
    sage: for i, r in enumerate(residuals): print(f"Segment {i}: {r}")
    """
    rp, rho = RamificationPoly(phi, alpha)   # have to make func for this
    LX = rho.parent()
    L = LX.base_ring()
    nualpha = nu(alpha)

    RL, lift = L.residue_field()
    RLz.<z> = RL[]

    slopes = [-m for m in reversed(LowerSlopes(rp))]
    vertices = list(reversed(LowerVertices(rp)))

    A = []

    for l in range(len(slopes)):
        m = slopes[l]
        i, vri = vertices[l]
        j, vrj = map(int, vertices[l+1])  # integerize

        t = m.numerator()
        d = m.denominator()

        a = sum(lift(Coefficient(rho, k*d + j) / (nualpha ** (vrj - k*t))) * z**k for k in range(int((i - j) / d) + 1))
        A.append(a)

    return A

def Distinguished(M, nu=None):
    """
    Given a set of reduced polynomials in Eisenstein form, return a distinguished polynomial.

    EXAMPLES:
    sage: K = Qp(5,prec=20)
    sage: R.<x> = K[]
    
    sage: phi1 = x^3 + 5*x + 5
    sage: phi2 = x^3 + 10*x + 5
    sage: phi3 = x^3 + 15*x + 5

    sage: M = {phi1, phi2, phi3}
    sage: phi_dist = Distinguished(M)
    sage: print(phi_dist)

    """
    
    L = list(M)
    R = parent(L[0])
    x = R.gen()
    
    # Determine nu
    K = L[0].base_ring()
    p = K.prime()  # uniformizer prime
    if is_eisenstein_form(L[0]):
        nu = x
    elif nu is None:
        nu = residue_factor(L[0], p)
    
    # Comparator key: evaluate expansion coefficients at p
    def sort_key(f):
        exp_coeffs = f.list()
        return tuple([c for c in exp_coeffs])

    # Sort L by the key
    L.sort(key=sort_key)
    return L[0]

def ResidualPolynomialClasses(phi, with_trans=False, conjugates=False):
    """
    The residual polynomial classes of an Eisenstein polynomial phi.
    
    EXAMPLES:
    sage: K = Qp(3, prec=20)
    sage: R.<x> = K[]
    sage: phi = x^2 - 3

    sage: ResidualPolynomialClasses(phi)
    """

    # Conj Eisenstein Form
    if not is_eisenstein_form(phi):
        conjugates = True
        phiE = EisensteinForm_simple(phi)
        # depending on what is returned by eisenstein form
        if isinstance(phiE, tuple) or isinstance(phiE, list):
            phi = phiE[0]
        else:
            phi = phiE

    Kx = phi.parent()
    K = phi.base_ring()
    RK, KtoRK = K.residue_field()
    n = phi.degree()

    def residual_polynomial_classes_sub(phi, with_trans):
        invA = set()
        for delta in RK:
            if delta != 0:
                deltaK = K(delta)
                phidelta = Kx([phi.coefficient(i) * deltaK**(n - i) for i in range(n + 1)])
                if with_trans:
                    res_poly = ResidualPolynomial(phidelta, Kx.gen(), phidelta.roots()[0][0])
                    invA.add((res_poly, phidelta, delta))
                else:
                    res_poly = ResidualPolynomial(phidelta, Kx.gen(), phidelta.roots()[0][0])
                    invA.add(res_poly)
        return invA

    if not conjugates:
        return residual_polynomial_classes_sub(phi, with_trans)
    else:
        invA = set()
        auts = K.automorphisms()
        for tau in auts:
            tauphi = Kx([tau(c) for c in phi.coefficients(sparse=False)])
            invA |= residual_polynomial_classes_sub(tauphi, with_trans)
        return invA

def PolynomialCompareLog(f, g):
    """
    Compare two polynomials f and g over a local field by comparing the
    discrete logarithms of their coefficients in lexicographic order
    (starting from the leading coefficient).

    EXAMPLES:
    
    sage: K = Qp(3, prec=10) 
    sage: R.<x> = K[]

    sage: f = x^2 + 3*x + 1
    sage: g = x^2 + 3*x + 2

    sage: res = PolynomialCompareLog(f,g)
    sage: print(res)
    """
    if f.degree() != g.degree():
        raise ValueError("Polynomials must have the same degree.")
    for i in reversed(range(f.degree() + 1)):
        a, b = f[i], g[i]
        if a == 0 and b != 0:
            return -1
        elif b == 0 and a != 0:
            return 1
        elif a != 0 and b != 0 and a != b:
            return discrete_log(a) - discrete_log(b)
    return 0

def ResidualPolynomialCompare(A, B):
    """
    Return 1 if A > B, -1 if A < B, 0 otherwise.

    EXAMPLES:

    sage: R.<x> = PolynomialRing(GF(7))

    sage: A = [x^2 + 3*x + 1, x^3 + 2]
    sage: B = [x^2 + 3*x + 1, x^3 + 3]

    sage: print(ResidualPolynomialCompare(A,B))
    """

    if len(A) != len(B):
        raise ValueError("ResidualPolynomialCompare: Lists of residual polynomials must be of the same length.")

    for a, b in zip(A, B):
        c = PolynomialCompareLog(a, b)
        if c != 0:
            return c

    return 0

def ResidualPolynomialDistinguished(phi, conjugates=False, constant_first=True):
    """
    The distinguished (minimal) representative of the residual polynomial class of an Eisenstein polynomial phi
along with the Eisenstein polynomials that yield the distinguished representative.
    """
    if not is_eisenstein_form(phi):
        conjugates = True
        ef = EisensteinForm_simple(phi)
        if isinstance(ef, (list, tuple)):
            phi = ef[0]
        else:
            phi = ef

    # Basic rings/fields
    K = phi.base_ring()
    p = K.prime()
    Kx = phi.parent()
    e = phi.degree()

    L = K.extension(phi, names=('alpha',))
    alpha = L.gen()

    rp, rho = RamificationPoly(phi, alpha)

    slopes = list(reversed([-m for m in LowerSlopes(rp)]))
    vertices = list(reversed(LowerVertices(rp)))

    Fq, KtoFq = K.residue_field()

    Fqz = PolynomialRing(Fq, 'z')
    z = Fqz.gen()
    q = Integer(Fq.cardinality())

    xi = Fq.multiplicative_generator()

    if Integer(phi.degree()) % Integer(p) != 0:
        A = ResidualPolynomial(phi, Kx.gen(), alpha)
        return A, [phi]

    def residual_polynomial_distinguished_sub(phi, constant_first=True):

        K = phi.base_ring()
        piK = K.uniformizer()

        Fq, KtoFq = K.residue_field()
        q = Fq.cardinality()

        #  constant_first branch
        if constant_first:
            phi0 = phi.constant_coefficient()
            phi01 = KtoFq(phi0 / piK) # residue
            a = discrete_log(phi01)        

            e = K.ramification_index()
            d, s0, _ = xgcd(e, q-1)

            k = a // d
            b = a % d

            t0 = (-s0 * k) % (q - 1)       
            Delta = (q - 1) // d
            x_base = [t0]

        else:
            Delta = 1
            x_base = [0]

        # Ramified Extensions
        L = K.extension(phi, names=('alpha',))
        alpha = L.gen()
        LX = PolynomialRing(L, 'X')
        X = LX.gen()

        rp, _ = RamificationPoly(phi, alpha)

        slopes = list(reversed([-m for m in LowerSlopes(rp)]))
        vertices = list(reversed(LowerVertices(rp)))
        A = ResidualPolynomial(phi, L['x'].gen(), alpha)

        g = 0

        # Main loop
        for idx in range(len(slopes)):
            m = slopes[idx]
            n = A[idx].degree()

            t = m.numerator()
            d = m.denominator()

            g = g + (d - t) * n

            
            for j in range(n, -1, -1):

                Aij = A[idx].coefficients(sparse=False)[j] if j <= n else 0

                if Aij != 0:
                    a = discrete_log(Aij) % (q - 1)

                    D = (Delta * ((t - d) * j + g)) % (q - 1)

                    if D != 0:
                        b, s, _ = xgcd(D, q - 1)

                        new_Delta = lcm(Delta, (q - 1) // b)
                        minexp = q # big 
                        new_x_base = []

                        for xij in x_base:
                            J = a + xij * ((t - d) * j + g)
                            r = J % b
                            k = J // b

                            x = (xij - k * s * Delta) % (q - 1)

                            if r < minexp:
                                minexp = r
                                new_x_base = [x]
                            elif r == minexp:
                                new_x_base.append(x)

                        Delta = new_Delta
                        x_base = new_x_base

        return x_base, Delta

    def residual_polynomial_phis(thisphi, s_base, s_diff):
        minphis = []
        deg = thisphi.degree()
        for sb in s_base:
            s = Integer(sb)
            # repeat loop until cycle returns to sb
            while True:
                s = Integer((s + s_diff) % Integer(q - 1))
                deltaK = K(xi ** Integer(s))
                coeffs = [thisphi.coefficient(i) * (deltaK ** (deg - i)) for i in range(0, deg + 1)]
                phidelta = Kx(coeffs)
                minphis.append((ResidualPolynomial(phidelta, Kx.gen(), alpha), phidelta))
                if s == sb:
                    break
        return minphis    
    
    As = []
    if not conjugates:
        base, delta = residual_polynomial_distinguished_sub(phi, constant_first=constant_first)
        As = residual_polynomial_phis(phi, base, delta)
    else:
        As = []
        auts = K.automorphisms()
        aut_maps = auts

        for tau in aut_maps:
            # apply automorphism tau to coefficients of phi
            tauphi = Kx([tau(c) for c in phi.coefficients(sparse=False)])
            base, delta = residual_polynomial_distinguished_sub(tauphi, constant_first=constant_first)
            As += residual_polynomial_phis(tauphi, base, delta)
        
        def cmp_as(a, b): # Slight modification of respolycompare for coeffs
            return int(ResidualPolynomialCompare(a[0], b[0]))

        As.sort(key=cmp_to_key(cmp_as))
    
    if len(As) == 0:
        return None, []
    
    target_respoly = As[0][0]
    philogs = []
    for a_res, a_phi in As:
        if a_res == target_respoly:
            const_div = a_phi.constant_coefficient() / piK
            mapped = KtoFq(const_div)
            philogs.append((Integer(discrete_log(mapped)), a_phi))

    if len(philogs) == 0: # special case if all res polys equal
        phis = [a_phi for (a_res, a_phi) in As if a_res == target_respoly]
        return target_respoly, phis

    minlog = min(pl[0] for pl in philogs)
    phis = [pl[1] for pl in philogs if pl[0] == minlog]

    return target_respoly, phis

def Expansion(f, nu):
    """
    The coefficients of the nu-expansion of f as a list.

    EXAMPLES:

    sage: f = 123
    sage: nu = 10
    sage: print(Expansion(f,nu))
    """
    expansion = []
    while f != 0:
        a = f % nu
        expansion.append(a)
        f = (f - a) // nu
    return expansion


def Contraction(L, nu):
    """
    Given list L = [a0, a1, ..., ak] of coefficients
    and polynomial nu, reconstruct poly.

    EXAMPLES:

    sage: L = [3, 2, 1]
    sage: nu = 10
    sage: print(Contraction(L,nu))
    """
    return sum(L[i] * nu**i for i in range(len(L)))

def IsMono(f):
    """
    True if the polynomial f is a monomial.

    EXAMPLES: 

    sage: R.<x> = PolynomialRing(QQ)
    sage: f = 3*x^2
    sage: print(IsMono(f))
    """

    R = f.parent().base_ring()
    coeffs = f.list()
    mono = (sum(1 for a in coeffs if a != 0) == 1)

    if not mono:
        return False

    if R is R.base_ring():
        return True

    coeff = sum(coeffs)
    listcoeff = coeff.list()
    ret = (sum(1 for a in listcoeff if a != 0) == 1)

    return ret

def Expansion2(f, nu, limit=0):
    """
    The nu-expansion of f such that its coefficients are given as p expansions and the nu-expansion of f.

    EXAMPLES:

    sage: Qp5 = Qp(5, prec=6)
    sage: Qp5.prime = lambda: 5
    sage: Qp5.precision = lambda: 6
    sage: R.<x> = PolynomialRing(Qp5)
    sage: f = 3+5*x+25*x^2
    sage: nu = x
    sage: Expansion2(f, nu)

    """

    K = f.parent().base_ring()
    if limit == 0:
        limit = K.precision()

    Zx = PolynomialRing(ZZ, 'x')

    nuexp = Expansion(f, nu)

    p = K.prime()

    if nu.degree() > 1:
        expansion = [Zx(a) for a in nuexp]
    else:
        expansion = [Zx(a.constant_coefficient().list()) for a in nuexp]

    expexp = []

    for g in expansion:
        h = g
        gel = []
        c = 0

        while (h != 0) and (c <= limit):
            gel.append(h % p)
            h = h // p     # integer division
            c += 1

        expexp.append(gel)

    maxlen = max(max(len(gel) for gel in expexp), limit)

    for i in range(len(expexp)):
        expexp[i] = expexp[i] + [0] * (maxlen - len(expexp[i]) + 1)

    return expexp, nuexp

def Contraction2(L, nu):
    """
    Contraction2(Expansion2(f,nu),nu) = f

    EXAMPLES:

    sage: R.<x> = PolynomialRing(Qp(3,8))
    sage: nu = x
    sage: L = [[2], [1,1], [0,0,1]]
    sage: print(Contraction2(L, nu))
    """

    Rx = nu.parent()
    R = Rx.base_ring()
    p = R.prime()

    # Coefs ints
    if R == R.prime_subring():
        return Rx(sum(sum((p**(j) * L[i][j] for j in range(len(L[i])))) * nu**i for i in range(len(L))))

    # Degree(nu) = 1, coefficients polys
    if nu.degree() == 1:
        coeffs = []
        for i in range(len(L)):
            c = sum(p**j * L[i][j](R.gen()) for j in range(len(L[i])))
            coeffs.append(c)
        return Rx(coeffs)

def RamificationPoly(phi, alpha):
    """
    Absolute ramification polygon and polynomial phi(alpha+x) of a polynomial phi in Eisenstein form, where alpha is a root of phi

    sage: K = Qp(5, 20)
    sage: R.<x> = PolynomialRing(K)
    sage: phi = x^3 + 5*x + 5      
    sage: alpha = phi.roots()[0][0]   
    sage: RamificationPoly(phi, alpha)
    """

    L = alpha.parent()
    Lx = PolynomialRing(L, 'x')
    x = Lx.gen()

    rho = Lx(phi)(x + alpha)
    ramification_polygon = rho.newton_polygon()

    return ramification_polygon, rho
