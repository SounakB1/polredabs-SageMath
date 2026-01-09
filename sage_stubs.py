"""
SageMath stub file to help language servers recognize Sage-specific syntax and functions.
This file is not meant to be executed - it's just for IDE support.
"""

# Type checking: ignore preparser syntax
# type: ignore

# SageMath preparser syntax support
# The preparser converts R.<x> = ... to R = ...; x = R.gen()
# We can't directly represent this in Python, but we can create stubs

# Common SageMath imports and functions
from typing import Any, Optional, Tuple, List, Dict

def GF(p: int, **kwargs: Any) -> Any:
    """Finite field of prime order p"""
    pass

def Qp(p: int, prec: Optional[int] = None, **kwargs: Any) -> Any:
    """p-adic field"""
    pass

def PolynomialRing(base_ring: Any, var: str = 'x', **kwargs: Any) -> Any:
    """Create a polynomial ring"""
    pass

def ZZ() -> Any:
    """Integer ring"""
    pass

def Integer(n: Any) -> Any:
    """Convert to Sage integer"""
    pass

def xgcd(a: Any, b: Any) -> Tuple[Any, Any, Any]:
    """Extended gcd"""
    pass

def lcm(a: Any, b: Any) -> Any:
    """Least common multiple"""
    pass

def parent(obj: Any) -> Any:
    """Get parent of object"""
    pass

def cmp_to_key(cmp_func: Any) -> Any:
    """Convert cmp function to key function"""
    pass

def Coefficient(f: Any, n: int) -> Any:
    """Get coefficient of polynomial"""
    pass

def conway_polynomial(p: int, n: int) -> Any:
    """Conway polynomial"""
    pass

def dilog(x: Any) -> Any:
    """Dilogarithm function"""
    pass

# SageMath's sage.all import
__all__ = [
    'GF', 'Qp', 'PolynomialRing', 'ZZ', 'Integer', 'xgcd', 'lcm',
    'parent', 'cmp_to_key', 'Coefficient', 'conway_polynomial', 'dilog'
]
def GF(p, **kwargs):
    """Finite field of prime order p"""
    pass

def Qp(p, prec=None, **kwargs):
    """p-adic field"""
    pass

def PolynomialRing(base_ring, var='x', **kwargs):
    """Create a polynomial ring"""
    pass

def ZZ():
    """Integer ring"""
    pass

def Integer(n):
    """Convert to Sage integer"""
    pass

def xgcd(a, b):
    """Extended gcd"""
    pass

def lcm(a, b):
    """Least common multiple"""
    pass

def parent(obj):
    """Get parent of object"""
    pass

def cmp_to_key(cmp_func):
    """Convert cmp function to key function"""
    pass

def Coefficient(f, n):
    """Get coefficient of polynomial"""
    pass

def conway_polynomial(p, n):
    """Conway polynomial"""
    pass

def dilog(x):
    """Dilogarithm function"""
    pass

# Common SageMath types that have special methods
class SageObject:
    def degree(self):
        pass
    
    def is_irreducible(self):
        pass
    
    def multiplicative_order(self):
        pass
    
    def valuation(self):
        pass
    
    def residue(self):
        pass
    
    def newton_polygon(self):
        pass
    
    def list(self):
        pass
    
    def coefficients(self, sparse=False):
        pass
    
    def constant_coefficient(self):
        pass
    
    def leading_coefficient(self):
        pass
    
    def change_ring(self, R):
        pass
    
    def subs(self, **kwargs):
        pass
    
    def roots(self, multiplicities=False):
        pass
    
    def factor(self):
        pass
    
    def is_zero(self):
        pass
    
    def gen(self):
        pass
    
    def base_ring(self):
        pass
    
    def parent(self):
        pass
    
    def characteristic(self):
        pass
    
    def prime(self):
        pass
    
    def precision(self):
        pass
    
    def uniformizer(self):
        pass
    
    def ramification_index(self):
        pass
    
    def inertia_degree(self):
        pass
    
    def degree(self):
        pass
    
    def extension(self, f, names=None):
        pass
    
    def residue_field(self):
        pass
    
    def automorphisms(self):
        pass
    
    def cardinality(self):
        pass
    
    def multiplicative_generator(self):
        pass
    
    def prime_subring(self):
        pass

# SageMath's preparser syntax
# R.<x> = PolynomialRing(...) gets converted to:
# R = PolynomialRing(...); x = R.gen()
# We can't directly represent this, but the language server should
# understand that after PolynomialRing(...), we can call .gen()

