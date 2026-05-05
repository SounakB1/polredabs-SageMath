from sage.all import *

def discrete_log(a): # Done
    return dilog(a)

def is_prim_pol(f, p): # Done
    """
    is pol irreducible and primitive?

    TESTS:

        sage: R.<x> = PolynomialRing(GF(7))
        
        sage: f = x^3 + 3*x + 2  # primitive
        sage: is_prim_pol(f, 7) 
        True

        sage: f = x^2 + 3 # reducible
        sage: is_prim_pol(f, 7) 
        False

        sage: f = x^2 + 1 # irreducible but not primitive
        sage: is_prim_pol(f, 7) 
        False
    """
    Fp = GF(p)
    m = f.degree()

    if not f.is_irreducible():
        return False

    K.<a> = GF(p**m, modulus=f)

    return a.multiplicative_order() == p**m - 1

def unram_pol_jr(p, m): # Done
    """
    TESTS:
        sage: pol = unram_pol_jr(5, 3)
        sage: pol 
        x^3 + 4 * x + 2

        sage: pol = unram_pol_jr(13, 8)
        sage: pol 
        x^8 + 4*x^2 + 12*x + 6
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

def conway_or_jr_polynomial(K, n): # Done (prob won't fix signature for p instead of K, useful in other places)
    """
    Return a Conway polynomial of degree n.

    EXAMPLES:
        sage: K = GF(7)
        sage: pol = conway_or_jr_polynomial(K, 3)
        sage: pol 
        x^3 + 6*x^2 + 4

        sage: K2 = GF(11)
        sage: pol = conway_or_jr_polynomial(K2,4)
        sage: pol 
        x^4 + 8*x^2 + 10*x + 2  
    """
    p = K.characteristic()
    if p == 0: # i.e. input is p-adic field
        try:
            p = K.prime()
        except Exception: # polynomial ring case
            base_ring = K.base_ring()
            p = base_ring.prime()
    try:
        return conway_polynomial(p, n)
    except Exception:
        return unram_pol_jr(p, n)

def is_conway_or_jr(nu):
    """
    EXAMPLES:

        sage: K = GF(7)
        sage: R.<x> = K[]
        sage: conway_or_jr_polynomial(K, 3)
        x^3 + 6*x^2 + 4

        sage: a = x^3 + 6*x^2 + 4
        sage: is_conway_or_jr(a)
        True

        sage: b = x^3 + 5*x
        sage: is_conway_or_jr(b)
        False
    """
    return conway_or_jr_polynomial(nu.parent(), nu.degree()) == nu

def residue_factor(phi, p): # Done
    """
    EXAMPLES:

        sage: R.<x> = PolynomialRing(GF(7))
        sage: phi = (x^2 + 3*x + 5)^2
        sage: nu = residue_factor(phi,7)
        sage: phi, nu 
        (x^4 + 6*x^3 + 5*x^2 + 2*x + 4, x^2 + 3*x + 5)

        sage: R.<x> = PolynomialRing(GF(11))
        sage: phi = x^3 + 4*x + 6 # not a power of irreducible polynomial
        sage: nu = residue_factor(phi, 11)
        sage: phi, nu 
        (x^3 + 4*x + 6, 'Phi is not a power of an irreducible polynomial.')

        sage: R.<x> = PolynomialRing(GF(3))
        sage: phi = (x^2 + x + 1)^2 # x^2 + x + 1 = (x+2)^2 is power of irreducible polynomial
        sage: nu = residue_factor(phi, 3)
        sage: phi, nu 
        (x^4 + 2*x^3 + 2*x + 1, x + 2)

        sage: R.<x> = PolynomialRing(GF(3))
        sage: phi = (x^2 + 2)^2 # x^2 + 2 is reducible and not power of deg 1 poly
        sage: nu = residue_factor(phi, 3)
        sage: phi, nu 
        (x^4 + x^2 + 1, 'Phi is not a power of an irreducible polynomial.')

        sage: R.<x> = PolynomialRing(GF(13))
        sage: phi = 13*x^5 + 26*x + 13 # 0 poly
        sage: nu = residue_factor(phi, 13)
        sage: phi, nu 
        (0, 'The inputted polynomial is 0.')
    """
    RZ = phi.parent()
    Fp = GF(p)

    Rp.<x> = PolynomialRing(Fp)
    coeffs_mod_p = [c % p for c in phi.list()]
    Rphi = Rp(coeffs_mod_p)

    if Rphi.is_zero():
        print("The inputted polynomial is 0.")
        return 0

    facs = Rphi.factor()
    if len(facs) != 1:
        print("Phi is not a power of an irreducible polynomial.")
        return 0

    nu = facs[0][0]  # irreducible factor mod p

    lifted = RZ([ZZ(c) for c in nu.list()])

    return lifted


def is_eisenstein_form(phi): # Done
    """
    True, if phi is in Eisenstein form.  If Conway is true the irreducible factor of phi in GF(p) must be a Conway polynomial.

    EXAMPLES:
        sage: K = Qp(3, 20)
        sage: R.<x> = K[]
        sage: phi = x^2 + 3*x + 3
        sage: is_eisenstein_form(phi) 
        True 

        # from polredabs.m

        sage: K = Qp(3, 20)
        sage: R.<x> = K[]
        sage: phi = x^6 + 246*x^4 + 84*x + 30
        sage: is_eisenstein_form(phi)
        True

        sage: K = Qp(3,20)
        sage: R.<x> = K[]
        sage: phi = x^3 + 3*x + 9
        sage: is_eisenstein_form(phi)
        False
    """
    K = phi.base_ring()
    if K.degree() != 1:
        return False
        
    nu = residue_factor(phi, K.prime())
    if nu == 0:
        return False
        
    if not nu.is_monic():
        return False
        
    nu_poly = K['x'](nu) 
    nuexp = Expansion(phi, nu_poly)
    
    coeffs_v = [a.valuation() for a in nuexp[0].coefficients()]
    if not coeffs_v or min(coeffs_v) != 1:
        return False
        
    for poly in nuexp[:-1]:
        if any(a.valuation() < 1 for a in poly.coefficients()):
            return False
            
    return True

def eisenstein_form(L, K): # Fixed
    """
    A generating polynomial phi in K[x] of L in Eisenstein form along with
    the polynomial nu generating the unramified subextensions of L/K and gamma with phi(gamma) = 0.

    EXAMPLES:
        sage: K = Qp(5, prec = 5, print_pos=False,print_mode="terse")
        sage: R.<x> = K[]
        sage: f = x^2-5
        sage: L.<a> = K.extension(f)
        sage: phi, nu, gamma = eisenstein_form(L, K)
        sage: phi, nu, gamma, phi(gamma)
        ((1 + O(5^5))*x^2 + O(5^6)*x - 5 + O(5^6), (1 + O(5^5))*x, a + O(a^11), O(a^12))

        sage: K = Qp(3, 20, print_pos=False,print_mode="terse")
        sage: R.<x> = K[]
        sage: f = x^2 - 3
        sage: L.<a> = K.extension(f)
        sage: phi, nu, gamma = eisenstein_form(L,K)
        sage: phi, nu, gamma, phi(gamma)
        ((1 + O(3^20))*x^2 + O(3^21)*x - 3 + O(3^21), (1 + O(3^20))*x, a + O(a^41), O(a^42))

        sage: K = Qp(3, 20, print_pos=False,print_mode="terse")
        sage: R.<x> = K[]
        sage: f = x^4 - 3
        sage: L.<a> = K.extension(f)
        sage: phi, nu, gamma = eisenstein_form(L,K)
        sage: phi, nu, gamma, phi(gamma)
        ((1 + O(3^20))*x^4 + O(3^21)*x^3 + O(3^21)*x^2 + O(3^21)*x - 3 + O(3^21), (1 + O(3^20))*x, a + O(a^81), O(a^84))

        sage: K = Qp(3, 20, print_pos=False,print_mode="terse")
        sage: R.<x> = K[]
        sage: f = x^5 + 3*x^3 + 6*x^2 + 3
        sage: L.<a> = K.extension(f)
        sage: phi, nu, gamma = eisenstein_form(L,K)
        sage: phi, nu, gamma, phi(gamma)
        ((1 + O(3^20))*x^5 + O(3^21)*x^4 + (3 + O(3^21))*x^3 + (6 + O(3^21))*x^2 + O(3^21)*x + 3 + O(3^21), 
        (1 + O(3^20))*x, a + O(a^101), O(a^105))
    """
    R = PolynomialRing(L, 't')
    t = R.gen()
    pi = L.uniformizer()

    if L.inertia_degree() == L.degree():
        n = L.inertia_degree()
        res = K.residue_field()
        Fp = res[0] if isinstance(res, (tuple, list)) else res
        nu = conway_or_jr_polynomial(Fp, n).change_ring(K)

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
        res = K.residue_field()
        Fp = res[0] if isinstance(res, (tuple, list)) else res
        nu = conway_or_jr_polynomial(Fp, n).change_ring(K)
        gamma = (R(nu - pi)).roots(multiplicities=False)[0]
        phi = gamma.minpoly(K)
        return phi, nu, gamma

def EisensteinForm_poly(f, K): # Gotta do oystein_poly_om for non-prime ring case  
    """
    Given f irreducible, return a polynomial g in Eisenstein form such that K[x]/(g)
    is isomorphic to the extension generated by f.

    TESTS:
        sage: K = Qp(5, prec=20, print_mode="terse")
        sage: R.<x> = K[]
        sage: f = x^2 + x + 2   # irreducible mod 5, not Eisenstein
        sage: phi, nu, gamma = EisensteinForm_poly(f, K)

        sage: phi
        (1 + O(5))*x^2 + (4 + O(5))*x + 2 + O(5)
        sage: nu
        (1 + O(5))*x^2 + (4 + O(5))*x + 2 + O(5)
        sage: gamma
        1 + beta + O(5)

        sage: K = Qp(5, prec=20, print_mode="terse")
        sage: R.<x> = K[]
        sage: f = x^3 - 5  # Not irreducible but eisenstein, should return itself
        sage: g, nu, alpha = EisensteinForm_poly(f, K)
        
        sage: g 
        x^3 - 5
        sage: nu
        (1 + O(5^20))*x
        sage: alpha
        alpha + O(alpha^61)

        sage: K = Qp(3, prec=20, print_mode="terse")
        sage: R.<x> = K[]
        sage: f = x^3 + 3*x + 9  
        sage: g, nu, alpha = EisensteinForm_poly(f, K) # Reducible, leads to type error
        Not irreducible.
    """
    L = K

    RL = L.residue_field()
    f = f.change_ring(L)
    if is_eisenstein_form(f):
        ext = L.extension(f, names=('alpha',))
        return eisenstein_form(ext, K)

    if f.change_ring(RL).is_irreducible():
        U = L.extension(f, names=('beta',))
        return eisenstein_form(U, K)

    fac = f.factor()
    if len(fac) != 1:
        print("Polynomial given not irreducible.")
        return 0
    residue_deg = fac[0][0].degree()
    # print(residue_deg)

    poly_for_U = conway_or_jr_polynomial(RL, residue_deg)
    U = L.extension(poly_for_U, 'u')

    fac2 = f.change_ring(U).factor()
    Ls = [U.extension(g[0], 'zeta') for g in fac2]
    return eisenstein_form(Ls[0], K)

def EisensteinForm_simple(f): # Done
    """
    Given f in K[x] irreducible, return a defining Oystein polynomial phi of L=K[x]/(f) 
  along with  the polynomial nu generating the unramified subextensions of 
  L/K and gamma with phi(gamma) = 0.
    """
    K = f.base_ring()
    return EisensteinForm_poly(f, K)

def ramification_poly_raw(phi, alpha): # Done
    # rho:=phi(alpha+x) and the Newton polygon of rho
    L = alpha.parent()

    Lx = PolynomialRing(L, 'x')
    x = Lx.gen()

    phi_L = Lx(phi)

    rho = phi_L(x + alpha)
    xpow = rho.valuation()

    # shift, since newton_polygon wants something with nonzero constant term
    ramification_polygon = (rho >> xpow).newton_polygon()
    if xpow != 0:
        # Need to shift back
        from sage.geometry.newton_polygon import NewtonPolygon
        ramification_polygon = NewtonPolygon([(x+xpow,y) for (x,y) in ramification_polygon.vertices()])

    return ramification_polygon, rho

def RamificationPoly(phi, nu, alpha): # Fixed
    """
    Ramification polygon and polynomial phi(alpha + nu(alpha) * x)
    of a nu-Oystein polynomial phi, where alpha is a root of phi.
    
    TESTS: 

    sage: K = Qp(3, prec=20, print_mode = "val-unit") 
    sage: R.<x> = K[]
    sage: phi = x^2 + 1  

    sage: S.<z> = K[]
    sage: nu = z

    sage: L.<alpha> = K.extension(phi)
    sage: ram_poly, rho = RamificationPoly(phi, nu, alpha)

    sage: print("Ramification polygon points:", ram_poly)
    Ramification polygon points: [(-1, 0), (-2, 0)]
    sage: print("Rho polynomial:", rho)
    Rho polynomial: (1 + O(3^20))*x^2 + (2 + O(3^20))*x
    """
    L = alpha.parent()
    
    Lx = PolynomialRing(L, 'x')
    x = Lx.gen()
    
    e = phi.degree() // nu.degree()
    nualpha = nu(alpha)
    
    rho = phi(nualpha * x + alpha) / (nualpha ** e)
    
    # newton polygon
    ramification_polygon = [(-i, rho.coefficient(i).valuation()) for i in range(1, rho.degree() + 1)]
    
    return ramification_polygon, rho

def LowerSlopes(f):
    np = f.newton_polygon()
    return [slope for slope, _ in np.lower_slopes()]

def LowerVertices(f):
    np = f.newton_polygon()
    return np.lower_vertices()

def ResidualPolys(phi, absolute=False):
    K = phi.base_ring()
    Kx = phi.parent()
    x = Kx.gen()

    if is_eisenstein_form(phi):

        L = K.extension(phi, names=('alpha',))
        alpha = L.gen()

        nu = x

        return ResidualPolynomial(phi, nu, alpha)

    # -------------------------------------------------
    # Case 2: absolute = True
    # -------------------------------------------------
    elif absolute:

        ef = EisensteinForm_simple(phi)

        if isinstance(ef, (list, tuple)):
            psi, nu, alpha = ef
        else:
            # safety fallback
            psi = ef
            L = K.extension(psi, names=('alpha',))
            alpha = L.gen()
            nu = psi.parent().gen()

        return ResidualPolynomial(psi, nu, alpha)

    else:

        ef = EisensteinForm_simple(phi)

        if isinstance(ef, (list, tuple)):
            _, nu, alpha = ef
        else:
            raise ValueError("EisensteinForm_simple did not return expected tuple.")

        pi = nu(alpha)

        psi = pi.minpoly()

        K2 = psi.base_ring()
        K2x = psi.parent()
        X = K2x.gen()

        psi = K2x(psi)

        L2 = K2.extension(psi, names=('beta',))
        beta = L2.gen()

        return ResidualPolynomial(psi, X, beta)

def ResidualPolynomialOfComponentAbs(phi, nu, alpha, m): # Fixed
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
        2*z, 3

        sage: phi = x^3 - 3
        sage: alpha_field = K.extension(phi, names='x')
        sage: alpha = alpha_field.gen()
        sage: nu = x
        sage: m = 1
        sage: Sm, cont = ResidualPolynomialOfComponentAbs(phi, nu, alpha, m)
        sage: print(Sm, ",", cont)
        z^3, 6
    """
    # Ramification Poly
    rp, rho = ramification_poly_raw(phi, alpha)
    LX = rho.parent()
    L = LX.base_ring()
    X = LX.gen()

    nualpha = nu(alpha)
    rhom = rho.subs(x=nualpha**(m+1) * X)

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

def ResidualPolynomial(phi, nu, alpha): # Fixed
    """
    The residual polynomials of the segments of the ramfication polygon of phi.
    alpha is a root of phi and nu(alpha) a uniformizing element in the extensions generated by alpha.
    
    EXAMPLES:

    sage: K = Qp(2, prec=20)
    sage: P.<x> = PolynomialRing(K)
    sage: phi = x^2 - 2
    sage: L.<a> = K.extension(phi)
    sage: alpha = a
    sage: nu = x

    sage: A = ResidualPolynos(phi, nu, alpha)
    sage: print("Residual Polynomials:", A)
    Residual Polynomials: [z + 1]

    sage: K = Qp(5, prec=20)
    sage: P.<x> = PolynomialRing(K)
    sage: phi = x^3 - 5
    sage: L.<a> = K.extension(phi)
    sage: alpha = a
    sage: nu = x

    sage: A = ResidualPolynos(phi, nu, alpha)
    sage: print("Residual Polynomials:", A)
    Residual Polynomials: [z^2 + 3*z + 3]
    """
    rp, rho = ramification_poly_raw(phi, alpha)
    
    LX = rho.parent()
    L = LX.base_ring()
    nualpha = nu(alpha)
    
    RL = L.residue_field()
    RLz = PolynomialRing(RL, 'z')
    z = RLz.gen()
    
    slopes = rp.slopes()
    vertices = rp.vertices()
    
    A = []
    
    for l in range(len(vertices)-1):
        j, vrj = vertices[l]    
        i, vri = vertices[l+1]   
        m = (vri - vrj) / (i - j)
        
        t = m.numerator()
        d = m.denominator()
        
        poly_coeffs = []
        upper_limit = int((i - j) / d)
        
        coeffs_sum = RLz(0)
        for k in range(upper_limit + 1):
            idx = int(k * d + j)
            raw_coeff = rho[idx]

            power = int(vrj + k * t) 
            term_val = raw_coeff / (nualpha**power)
            
            coeffs_sum += RL(term_val) * (z**k)
            
        A.append(coeffs_sum)

    return A[::-1] # reverse

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

    rp, rho = ramification_poly_raw(phi, alpha)

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

        rp, _ = ramification_poly_raw(phi, alpha)

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

def PolToFieldElt(K, g):
    """
    Evaluates the integer polynomial g at the generator of K, reduced mod the
    defining polynomial.  Equivalent to g(K.gen()) but works over ZZ[x].
    
    EXAMPLES:
    sage: R.<x> = ZZ[]
    sage: K.<a> = NumberField(x^2 - 2)

    sage: g = x^2 + 3*x + 1
    sage: elt = PolToFieldElt(K, g)

    """
    ZZx = PolynomialRing(ZZ, 'x')
    QQx = PolynomialRing(QQ, 'x')
    h = QQx(g) % QQx(K.defining_polynomial())
    n = K.degree()
    coeffs = h.padded_list(n)
    return K(coeffs)
 
def ResidueField(P_data):
    return P_data['residue_field']
 
def Lift(res_elt, P_data):
    """
    Lifts a residue-field element to an element of the number field K.
 
    Magma calls LocalLift then PolToFieldElt.  For our purposes (used in
    oystein_poly_om to lift roots of nu-bar to K) we just need to represent
    the residue element as a number-field element.  Since kp = GF(p^f) and
    the prime ideal P has inertia degree f, we express res_elt in the
    power basis of GF(p^f) and lift those integer coefficients to K.
    """
    K = P_data['number_field']
    kp = P_data['residue_field']
    p = P_data['p']
 
    coeffs_Fp = res_elt.polynomial().padded_list(kp.degree())
 
    ZZx = PolynomialRing(ZZ, 'x')
    g = ZZx([ZZ(c) for c in coeffs_Fp])
    return PolToFieldElt(K, g)

def Montes_number_field(phi_ZZ, p):
    """
    Runs the Montes algorithm on K = QQ[x]/(phi_ZZ) at the prime p and
    returns a dict with the prime-ideal data for the unique prime above p.
 
    Montes.m sets:
        K`PrimeIdeals[p,1]`e -> P_data['e']
        K`PrimeIdeals[p,1]`f -> P_data['f']
        K`LocalIndex[p] -> P_data['local_index']
        K`PrimeIdeals[p,1]`LocalGenerator -> P_data['local_generator']
        ResidueField(P) -> P_data['residue_field']
    """
    ZZx = PolynomialRing(ZZ, 'x')
    QQx = PolynomialRing(QQ, 'x')
 
    K = NumberField(phi_ZZ, 'a')
    ZK = K.maximal_order()
    p = ZZ(p)
 
    # K`LocalIndex[p] = v_p([ZK : Z[a]])
    disc_val = ZZ(K.discriminant()).abs().valuation(p)
    order_Za = K.order(K.gen())
    try:
        idx = ZK.index_in(order_Za) # [ZK : Z[a]]
    except Exception:
        idx = ZZ(1)
    local_index = ZZ(idx).valuation(p)
 
    # oystein_poly_om assumes phi is p-adically irreducible
    pfact = K.factor(p)  
    P_sage = pfact[0][0]
    e = ZZ(pfact[0][1]) # ramification index = exponent
    f = ZZ(P_sage.residue_field().degree())
 
    kp = P_sage.residue_field() 
 
    # We need an element piK of K with v_P(piK) = 1.
    # SageMath's two-element generators for P are (p, g(a)) where g(a) has v_P = 1 when e > 1, or we use p when e = 1.
    gens_P = list(P_sage.gens_two()) 
    piK = None
    for g_elt in gens_P:
        g_K = K(g_elt)
        try:
            v = P_sage.valuation(ZK(g_K))
            if v == 1:
                piK = g_K
                break
        except Exception:
            continue
    if piK is None:
        # Fallback - p has valuation e, use K(p) if e=1
        piK = K(p) if e == 1 else K(gens_P[-1])
 
    return {
        'e':               e,
        'f':               f,
        'local_index':     local_index,
        'disc_val':        disc_val,
        'local_generator': piK,
        'residue_field':   kp,
        'number_field':    K,
        'p':               p,
        'prime_ideal':     P_sage,
    }
 
def CharacteristicPoly(phip, alpha_QQ, phi_ZZ, Zpp):
    """
    Compute the characteristic polynomial of alpha (given as a QQ-polynomial
    reduced mod phi_ZZ) acting on Zpp[x]/(phip) by multiplication.
    """
    QQx = PolynomialRing(QQ, 'x')
    Zppx = PolynomialRing(Zpp, 'x')
    n = phi_ZZ.degree()
 
    # Build the multiplication-by-alpha matrix over QQ, mod phi_ZZ
    phi_QQ = QQx(phi_ZZ)
    alpha_red = QQx(alpha_QQ) % phi_QQ
 
    # Column j = (x^j * alpha_red) mod phi_QQ, written in basis {1,x,...,x^{n-1}}
    cols = []
    for j in range(n):
        col = (QQx.gen()**j * alpha_red) % phi_QQ
        cols.append(col.padded_list(n))
 
    M = matrix(QQ, n, n, [cols[j][i] for i in range(n) for j in range(n)])
    char_QQ = M.charpoly()
 
    return Zppx([Zpp(c) for c in char_QQ.list()])

def PolRedPadicTame(phi): # Works
    """
    EXAMPLES:
    
    sage: K = Qp(5, prec=30)
    sage: R.<x> = K[]

    sage: phi = x^3 + 5*x + 10  

    sage: psi = PolRedPadicTame(phi)
    sage: psi
    (1 + O(5^30))*x^3 + 5 + O(5^2)
    """
    K = phi.base_ring()
    p = K.prime()
    e0 = phi.degree()

    if e0 % p == 0:
        raise ValueError("PolRedPadicTame works for tamely ramified extensions only")
    if not phi.is_eisenstein():
        raise ValueError("PolRedPadicTame works for Eisenstein polynomials only")

    R.<x> = PolynomialRing(K)
    pi = K.uniformizer()

    # residue field
    U = K.residue_field()
    xi = U.multiplicative_generator()

    phi0 = phi.constant_coefficient()
    phi01 = U(phi0 / pi)    

    l = phi01.log(xi)
    b = gcd(e0, p - 1)
    r = l % b

    psi = x**e0 + pi * K(xi^r)
    return psi
 
def pol_red_padic_sub(Phi, nu, alpha, psi01):
    """
    Given a nu-Oystein polynomial Phi in K[x], a root alpha of Phi in L = K(alpha),
    and the desired constant coefficient psi01 mod pi^2 (as a residue-field element),
    Krasner-Monge reduction level by level and return a set of candidate
    reduced polynomials (each paired with the corresponding root in L).
    
    EXAMPLES:
        sage: K = Qp(3, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^3 + 3
        sage: L.<alpha> = K.extension(phi)
        sage: nu = x
        sage: psi01 = K.residue_field()(1)
        sage: M = pol_red_padic_sub(phi, R(nu), alpha, psi01)
        sage: print(len(M))
 
        sage: K = Qp(2, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^2 + 2
        sage: L.<alpha> = K.extension(phi)
        sage: nu = x
        sage: psi01 = K.residue_field()(1)
        sage: M = pol_red_padic_sub(phi, R(nu), alpha, psi01)
        sage: print(len(M))
 
        sage: K = Qp(5, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^5 + 5
        sage: L.<alpha> = K.extension(phi)
        sage: nu = x
        sage: psi01 = K.residue_field()(1)
        sage: M = pol_red_padic_sub(phi, R(nu), alpha, psi01)
        sage: print(len(M))
    """
    n = Phi.degree()
    f = nu.degree()
    e = n // f
 
    Kx = Phi.parent()
    K = Kx.base_ring()
    p = K.prime()
 
    L = alpha.parent()
    Lt = PolynomialRing(L, 't')
 
    RL, LtoRL = L.residue_field(True)  
    Fp = RL.prime_subfield()
    RLz = PolynomialRing(RL, 'z')
 
    psi01R = RL(psi01)
    Pi = nu.change_ring(L)(alpha)   # nu(alpha), the uniformiser of L
 
    A_phi = ResidualPolynomial(Phi, nu, alpha)
 
    # Compute ramification polygon and easy-reduction parameters
    rp_list, rho = RamificationPoly(Phi, nu, alpha)
    from sage.geometry.newton_polygon import NewtonPolygon
    rp = NewtonPolygon(rp_list)
 
    slopes_all = [s for s in rp.slopes() if abs(s) < K.precision_cap()]
    if not slopes_all:
        # Totally tame – no wild reduction needed; return Phi unchanged
        return {(Phi, alpha)}
 
    maxslope = max(slopes_all)
    easystart = int(floor(maxslope)) + 2
 
    Smax, PHImax = ResidualPolynomialOfComponentAbs(Phi, nu, alpha, easystart - 1)
    easylimit = PHImax // e + 1
 
    # Helper: set all expansion digits above the easy threshold to zero
    def easyreduce(phi):
        nuexp, _ = Expansion2(phi, nu, limit=easylimit)
        m = easystart
        while True:
            wm = PHImax + m - easystart
            i  = wm % e
            k  = wm // e
            if k > easylimit or k >= K.precision_cap():
                break
            if k < len(nuexp[i]):
                nuexp[i][k] = 0
            m += 1
        return Contraction2(nuexp, nu)
 
    # m = 0 step
    nuexp2, nuexp = Expansion2(Phi, nu, limit=easylimit)
    nualpha = Pi
    eta = LtoRL(nualpha**e / p)
    S1, r1 = ResidualPolynomialOfComponentAbs(Phi, nu, alpha, 0)
    S1eta = eta * S1
    
    if alpha.valuation() == 0:
        gamma = LtoRL(alpha)
    else:
        gamma = RL.gen()
 
    phi01 = RL(nuexp2[0][1](gamma) if callable(nuexp2[0][1]) else nuexp2[0][1])
 
    # Roots of S1eta - (phi01 - psi01R) give the required shifts theta
    target_poly = S1eta - RLz(phi01 - psi01R)
    Thetas = [r for r, _ in target_poly.roots()]
    if not Thetas:
        raise ValueError("pol_red_padic_sub: reduction step m=0 failed (no roots)")
 
    new_phis = set()
    for theta in Thetas:
        new_beta = alpha + L(theta) * nualpha
        new_phi = new_beta.minpoly(K)   # characteristic polynomial over K
        new_phi = Kx(new_phi)
        if is_eisenstein_form(Phi):
            if ResidualPolynomial(new_phi, nu, new_beta) == A_phi:
                new_phis.add((new_phi, new_beta))
        else:
            new_phis.add((new_phi, new_beta))
 
    M = new_phis
 
    for m in range(1, easystart):
        new_M = set()
        for phi, beta in M:
            nuexp2_b, nuexp_b = Expansion2(phi, nu, limit=easylimit)
            nubeta = nu.change_ring(L)(beta)
            eta_b  = LtoRL(nubeta**e / p)
 
            Am, PHIm = ResidualPolynomialOfComponentAbs(phi, nu, beta, m)
            i_idx = PHIm % e
            k_idx = PHIm // e
 
            # phisik: the (i,k) digit of the expansion of phi
            raw = nuexp2_b[i_idx][k_idx] if k_idx < len(nuexp2_b[i_idx]) else 0
 
            if beta.valuation() == 0:
                gamma_b = LtoRL(beta)
            else:
                gamma_b = RL.gen()
 
            phisikbeta = RL(raw(gamma_b) if callable(raw) else raw)
 
            # Build the image matrix of eta^k * Am to find the reduction
            FB = RL.basis_over(Fp)
            FL = [list((eta_b**k_idx * Am)(b)) for b in FB]
            FM = matrix(Fp, FL)
 
            from sage.geometry.newton_polygon import NewtonPolygon as _NP
            Mecho = FM.echelon_form()
            vdelta = vector(Fp, list(phisikbeta)[::-1])
            jB = 0
            iB = 0
            done = False
            while iB < len(FB) and not done:
                while Mecho[iB][jB] == 0 and not done:
                    if jB < len(FB) - 1:
                        jB += 1
                    else:
                        done = True
                if not done:
                    vb  = vector(Fp, Mecho[iB])
                    ab  = vdelta[jB] / vb[jB]
                    vdelta = vdelta - ab * vb
                    iB += 1
 
            delta = RL(list(reversed(list(vdelta))))
 
            # Solve FM * sol = phisikbeta - delta for the shift theta
            rhs = vector(Fp, list(phisikbeta - delta))
            try:
                sol, kernel = FM.solve_right(rhs), FM.right_kernel()
                Thetas_m = [RL(list(sol + k)) for k in kernel.basis()] if kernel.dimension() > 0 else [RL(list(sol))]
            except Exception:
                Thetas_m = []
 
            for theta in Thetas_m:
                new_beta2 = beta + L(theta) * nubeta**(m + 1)
                new_phi2 = Kx(new_beta2.minpoly(K))
                new_M.add((new_phi2, new_beta2))
 
        M = new_M
 
    # Apply easy reduction and return the polynomial set
    return {easyreduce(phibeta[0]) for phibeta in M}
 
 
def PolRedPadicTame_full(Phi, nu, alpha, distinguished=True, conjugates="auto"):
    """
    Reduction of a tamely ramified Eisenstein polynomial Phi, given the
    unramified part nu and a root alpha of Phi.  Returns the distinguished
    reduced polynomial (or a set of candidates if distinguished=False).
 
    EXAMPLES:
        sage: K = Qp(5, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^3 + 5
        sage: L.<alpha> = K.extension(phi)
        sage: psi = PolRedPadicTame_full(phi, R(x), alpha)
        sage: print(psi)
 
        sage: K = Qp(7, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^5 + 7
        sage: L.<alpha> = K.extension(phi)
        sage: psi = PolRedPadicTame_full(phi, R(x), alpha)
        sage: print(psi)
 
        sage: K = Qp(11, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^3 + 11
        sage: L.<alpha> = K.extension(phi)
        sage: psi = PolRedPadicTame_full(phi, R(x), alpha)
        sage: print(psi)
    """
    K  = Phi.base_ring()
    Kx = Phi.parent()
    L = alpha.parent()
    p = L.prime()
 
    if conjugates == "auto":
        conjugates = (nu.degree() != 1)
 
    # The defining polynomial of L and its base (possibly unramified) ring
    phi_L = L.defining_polynomial()
    Lur = phi_L.base_ring()
    Lurx = PolynomialRing(Lur, 'x')
    U, LurtoU = Lur.residue_field(True)
    e0 = phi_L.degree()
 
    if conjugates and nu.degree() != 1:
        phis_set = {Lurx([tau(c) for c in phi_L.coefficients(sparse=False)])
                   for tau in Lur.automorphisms()}
    else:
        phis_set = {phi_L}
 
    M = set()
    for tauphi in phis_set:
        # tame reduction of this conjugate
        psi = PolRedPadicTame(Lurx(tauphi).change_ring(Lur))
        if nu.degree() == 1:
            M.add(psi.change_ring(K))
        else:
            psi0 = psi.constant_coefficient()
            psi01 = LurtoU(psi0 / Lur.uniformizer())
            # express psi01 in the K-basis and form the K[x] polynomial
            psi01_K = Kx([K(c) for c in psi01.polynomial().padded_list(nu.degree())])
            Psi = nu**e0 + psi01_K * p
            M.add(Psi)
 
    if distinguished:
        return Distinguished(M, nu=nu if nu.degree() != 1 else None)
    return M
 
def PolRedPadic_full(Phi, nu, alpha, distinguished=True, conjugates="auto"):
    """
    Phi in K[x] in Eisenstein form, Phi(alpha) = 0, nu(alpha) uniformizer of K(alpha).
    Return the Krasner-Monge reduction of Phi.
 
    EXAMPLES:
        sage: K = Qp(3, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^3 + 3
        sage: L.<alpha> = K.extension(phi)
        sage: psi = PolRedPadic_full(phi, R(x), alpha)
        sage: print(psi)
 
        sage: K = Qp(2, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^4 + 2
        sage: L.<alpha> = K.extension(phi)
        sage: psi = PolRedPadic_full(phi, R(x), alpha)
        sage: print(psi)
 
        sage: K = Qp(5, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^5 + 5
        sage: L.<alpha> = K.extension(phi)
        sage: psi = PolRedPadic_full(phi, R(x), alpha)
        sage: print(psi)
    """
    Kx = Phi.parent()
    K = Kx.base_ring()
    L = alpha.parent()
    p = L.prime()
 
    if conjugates == "auto":
        conjugates = (nu.degree() != 1)
 
    RL, LtoRL = L.residue_field(True)
    U = L.base_ring() if hasattr(L, 'base_ring') else K
 
    pi = L.uniformizer()
    psi_L = L.defining_polynomial()
 
    # gamma: root of nu in L  (nu(gamma) = pi)
    gamma_roots = (nu.change_ring(L) - pi).roots()
    gamma = gamma_roots[0][0]
 
    # char poly of gamma over the prime subfield of K
    phi_gamma = gamma.minpoly(K)
    phi_gamma = Kx(phi_gamma)
 
    # Find distinguished residual polynomial representative
    A, psis = ResidualPolynomialDistinguished(psi_L, conjugates=conjugates,
                                              constant_first=True)
 
    M = set()
    for psi in psis:
        # Get Eisenstein form of psi
        ef = EisensteinForm_simple(Kx(psi))
        if isinstance(ef, (list, tuple)):
            thisphi, nu_ef, thisalpha = ef
        else:
            thisphi  = ef
            L2 = K.extension(thisphi, names=('a',))
            thisalpha = L2.gen()
            nu_ef = thisphi.parent().gen()
 
        psi01 = psi.constant_coefficient() / p
        # psi01 as a residue-field element
        psi01_res = RL(psi01) if psi01 in RL else LtoRL(L(psi01))
 
        newphis = pol_red_padic_sub(thisphi, Kx(nu_ef), thisalpha, psi01_res)
        M |= newphis
 
    if distinguished:
        return Distinguished(M)
    return M
 
 
def PolRedPadic(Phi, K=None, distinguished=True, conjugates="auto"):
    """
    For Phi in O_K irreducible, return a Krasner-Monge reduced polynomial Psi
    such that K[x]/(Phi) is isomorphic to K[x]/(Psi).
 
    When K is omitted the coefficient ring of Phi is used.  Accepts both
    p-adic coefficient rings and integer coefficient rings (with a precision
    keyword available via the integer overload below).
 
    EXAMPLES:
        sage: K = Qp(3, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^3 + 3*x + 3
        sage: print(PolRedPadic(phi))
 
        sage: K = Qp(5, prec=20)
        sage: R.<x> = K[]
        sage: phi = x^5 + 5*x + 5
        sage: print(PolRedPadic(phi))
 
        sage: K = Qp(2, prec=30)
        sage: R.<x> = K[]
        sage: phi = x^4 + 2*x + 2
        sage: print(PolRedPadic(phi))
    """
    if K is None:
        K = Phi.base_ring()
 
    p = K.prime()
 
    # Convert to Eisenstein / Oystein form
    ef = EisensteinForm_simple(Phi.change_ring(K))
    if isinstance(ef, (list, tuple)):
        phi, nu, alpha = ef
    else:
        phi = ef
        L = K.extension(phi, names=('a',))
        alpha = L.gen()
        nu = phi.parent().gen()
 
    L = alpha.parent()
 
    # Dispatch: tame vs wild
    if L.ramification_index() % p != 0:
        M = PolRedPadicTame_full(phi, phi.parent()(nu), alpha, distinguished=distinguished, conjugates=conjugates)
    else:
        M = PolRedPadic_full(phi, phi.parent()(nu), alpha, distinguished=distinguished, conjugates=conjugates)
    return M
 
 
def PolRedPadic_ZZ(f, p, prec=300, distinguished=True):
    """
    The distinguished reduced generating polynomial of the extension generated
    by f (a polynomial over ZZ) over Zp.
 
    EXAMPLES:
        sage: R.<x> = ZZ[]
        sage: f = x^3 + 3
        sage: print(PolRedPadic_ZZ(f, 3))
 
        sage: R.<x> = ZZ[]
        sage: f = x^2 + 2
        sage: print(PolRedPadic_ZZ(f, 2))
 
        sage: R.<x> = ZZ[]
        sage: f = x^4 + 5
        sage: print(PolRedPadic_ZZ(f, 5))
    """
    Zp  = Qp(p, prec)   # use Qp for convenience; coefficients land in Zp
    ZpX = PolynomialRing(Zp, 'X')
    Phi = ZpX(f)
    Psi = PolRedPadic(Phi, Zp, distinguished=distinguished, conjugates="auto")
    return Psi
