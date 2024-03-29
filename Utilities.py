

import sys, os
# in my environment, without following codes, sagemath doctest fails to import SymbolicMultipleZetaValues
if os.getcwd() not in sys.path:
    sys.path.append(os.getcwd())
import SymbolicMultipleZetaValues
import functools
import itertools
from functools import lru_cache
from sage.all import *

def powerset(seq, m):
    return [ list(u) for u in itertools.product(*([seq]*m) ) ]

def multiple_zeta(*ks):
    return SymbolicMultipleZetaValues.symbolic_multiple_zeta(*ks)

# For FormalSum
def lift_to_fs(v):
    return FormalSum([(1,v)])

import functools
import itertools
def LiftFormalSum_with_zero(func,zero):
    def lift_to_fs(v):
        return FormalSum([(1,v)])
    @functools.wraps(func)
    def wrapper(*args, **kwags):
        formal_sums = [lift_to_fs(obj) if not isinstance(obj,FormalSum) else obj for obj in args]
        ret = zero
        for formal_sum_arg in itertools.product(*formal_sums):
            coeff = mul(c for c,v in formal_sum_arg )
            arg = tuple(v for c,v in formal_sum_arg )
            ret += coeff * func(*arg, **kwags)
        return ret
    return wrapper

def LiftFormalSum(zero):
    return (lambda func: LiftFormalSum_with_zero(func, zero) )

# For lindep
prec = 200
REAL = RealField(prec)
def powerset(seq, m):
    import itertools
    return [ list(u) for u in itertools.product(*([seq]*m) ) ]
def get_linear_relation(vals):
    rels = gp.lindep(vals + [min(vals)*REAL(exp(1))] ).sage()
    assert rels[-1] == 0
    return rels[:-1]
def check_lindep(vals):
    rels = gp.lindep(vals + [min(vals)*REAL(exp(1))] ).sage()
    return (rels[:-1], rels[-1]==0)
def exist_linear_relation(vals):
    rels = gp.lindep(vals + [min(vals)*REAL(exp(1))] ).sage()
    return rels[-1] == 0

#multiple harmonic sum
def mhs(ks, p):
    u = [1]*p
    for k in ks:
        u2 = [0]*p
        for n in xrange(1,p):
            u2[n] = ( u2[n-1] + u[n-1] * (n*1)^(-k) )
        u = u2
    return u[p-1]

#dual
@LiftFormalSum(FormalSum(0))
def HoffmanDual(ks):
    r"""
    Description:

        Calculate the Hoffman dual index

    Input:

        ks - tuple of integers

    Output:

        tuple of integers, Hoffman dual index of ks

    EXAMPLES::
        sage: HoffmanDual((2,3))
        (1, 2, 1, 1)
    """
    s = ""
    for i,k in enumerate(ks):
        if i!=0:
            s+=","
        s += "+"*(k-int(1) )
    ret = [1]
    for c in s:
        if c=="+":
            ret.append(1)
        elif c==",":
            ret[-1]+=1
        else:
            assert False
    return lift_to_fs(tuple(ret))

@LiftFormalSum(FormalSum(0))
def phiDual(ks):
    r"""
    Description:

        Calculate the phi dual index

    Input:

        ks - tuple of integers

    Output:

        FormalSum of tuple of integers, phi dual index of ks

    Examples::
        sage: phiDual((1,))
        -(1,)

        sage: phiDual((2,))
        -(1, 1) - (2,)

        sage: phiDual((1,2))
        (1, 1, 1) + (1, 2)

        sage: phiDual(phiDual((2,3,5)))
        (2, 3, 5)

    """
    def all_refinement(ls):
        ls = tuple(ls)
        if len(ls)==0:return [()]
        return [(p,)+seq for p in range(1,ls[0]) for seq in all_refinement( (ls[0]-p,)+ls[1:] )  ] \
                + [(ls[0],)+seq for seq in all_refinement(ls[1:]) ]
    return FormalSum([((-1)**len(ks),tuple(ls) ) for ls in all_refinement(ks)])

#harmonic_product
@LiftFormalSum(FormalSum(0))
def harmonic_product(ks,ls):
    r"""
    Description:

        Calculate harmonic product of inputs

    Input:

        ks - tuple of integers
        ls - tuple of integers

    Output:

        FormalSum of tuple of integers, harmonic product of ks and ls

    Examples::
        sage: harmonic_product((3,), (5,))
        (3, 5) + (5, 3) + (8,)
    """
    self = harmonic_product
    @LiftFormalSum(FormalSum(0))
    def Concatenate(seq1,seq2):
        return lift_to_fs(seq1+seq2)

    self = harmonic_product
    if len(ks)==0 or len(ls)==0:
        return lift_to_fs(ks+ls)
    return Concatenate(ks[:1], self(ks[1:],ls) ) + \
            Concatenate(ls[:1], self(ks,ls[1:])) + \
            Concatenate((ks[0]+ls[0],), self(ks[1:],ls[1:]))


@LiftFormalSum(FormalSum(0))
def HarmonicStarProduct(ks,ls):
    r"""
    Description:

        Calculate harmonic product for star index

    Input:

        ks - tuple of integers
        ls - tuple of integers

    Output:

        FormalSum of tuple of integers, phi dual index of ks

    Examples::
        sage: HarmonicStarProduct((3,), (5,))
        (3, 5) + (5, 3) - (8,)
    """
    self = HarmonicStarProduct
    @LiftFormalSum(FormalSum(0))
    def Concatenate(seq1,seq2):
        return lift_to_fs(seq1+seq2)

    self = harmonic_product
    if len(ks)==0 or len(ls)==0:
        return lift_to_fs(ks+ls)
    return Concatenate(ks[:1], self(ks[1:],ls) ) + \
            Concatenate(ls[:1], self(ks,ls[1:])) - \
            Concatenate((ks[0]+ls[0],), self(ks[1:],ls[1:]))

@LiftFormalSum(FormalSum(0))
def HarmonicRegularization(ks, T = 0):
    r"""
    Description:

        Calculate harmonic regularization of ks

    Input:

        ks - tuple of integers
        T -

    Output:

        FormalSum of tuple of integers, harmonic regularization of ks

    Examples::
        sage: HarmonicRegularization((1, 1))
        -1/2*(2,)

        sage: T = PolynomialRing(QQ, "T").gen(0)
        sage: HarmonicRegularization((1, 1), T = T)
        -1/2*(2,) + 1/2*T^2*()

        sage: T = PolynomialRing(QQ, "T").gen(0)
        sage: HarmonicRegularization((2, 1), T = T)
        -(1, 2) - (3,) + T*(2,)

        sage: HarmonicRegularization((1, 3, 5))
        (1, 3, 5)
        sage: HarmonicRegularization(harmonic_product((1,),(3,5,1)))
        0

        sage: U = PolynomialRing(QQ, "U").gen(0)
        sage: HarmonicRegularization(harmonic_product((1,),(1,3,5)), T = U)
        U*(1, 3, 5)
    """
    num_of_ones_at_end = len(ks) - min(s for s in range(len(ks)+1) if all(k==1 for k in ks[s:]) )
    if num_of_ones_at_end == 0:
        return lift_to_fs(ks)
    else:
        val = lift_to_fs(ks) - Integer(1) / num_of_ones_at_end * harmonic_product(ks[:-1],ks[-1:])
        res = HarmonicRegularization(val, T=T)
        if T!=0:
            res += T * HarmonicRegularization(ks[:-1], T=T) / num_of_ones_at_end
        return res


def generate_all_index(weight):
    self = generate_all_index
    if weight < 0:return []
    if weight==0:return [()]
    return [seq+(k,) for k in range(1,weight+1) for seq in self(weight-k)]

def generate_all_index_with_depth(weight, depth):
    self = generate_all_index_with_depth
    if weight < 0 or depth<0:return []
    if weight==0 and depth==0:return [()]
    return [seq+(k,) for k in range(1,weight+1) for seq in self(weight-k,depth-1)]


def generate_all_index_admit_zero(weight, depth):
    self = generate_all_index_admit_zero
    if depth==0:return [()] if weight==0 else []
    if depth==1:return [(weight,)]
    return [seq+(k,) for k in range(weight+1) for seq in self(weight-k,depth-1)]


def generate_all_Hoffman_index(weight):
    if weight==0:return [()]
    if weight<0 or weight==1:return []
    return [(k,)+seq for k in [2,3] for seq in generate_all_Hoffman_index(weight-k)]

def generate_all_admissible_Euler_index(weight):
    self = generate_all_admissible_Euler_index
    if weight < 0:return []
    if weight==0:return [()]
    dep1 = [(-1,)] if weight==1 else [(weight,),(-weight,)]
    return dep1 + [(k*e,)+seq for e in [1,-1] for k in range(1,weight) for seq in self(weight-k)]

def generate_all_Euler_index(weight):
    self = generate_all_admissible_Euler_index
    if weight < 0:return []
    if weight==0:return [()]
    dep1 = [(weight,),(-weight,)]
    return dep1 + [(k*e,)+seq for e in [1,-1] for k in range(1,weight) for seq in self(weight-k)]

def set_shuffle_index(ks,ls):
    self = set_shuffle_index
    if len(ks)==0 or len(ls)==0:
        return [ks+ls]
    return [ks[:1]+seq for seq in self(ks[1:],ls)]+[ls[:1]+seq for seq in self(ks,ls[1:])]
@LiftFormalSum(FormalSum(0))
def shuffle_index(ks,ls):
    return FormalSum([(1,ms) for ms in set_shuffle_index(ks,ls)])

@LiftFormalSum(FormalSum(0))
@lru_cache()
def shuffle_product_of_word(word_1,word_2):
    r"""
    Description:

        Calculate shuffle products of inputs

    Input:

        word_1, word_2 - sentence of "xy"

    Output:

        FormalSum of sentences of "xy", shuffle product of word_1 and word_2

    Examples::
        sage: shuffle_product_of_word("xx","y")
        xxy + xyx + yxx
    """
    assert (c=="x" or c=="y" for word in (word_1,word_2) for c in word)
    self = shuffle_product_of_word
    if len(word_1)==0 or len(word_2)==0:
        return lift_to_fs(word_1+word_2)

    @LiftFormalSum(FormalSum(0))
    def Concatenate(seq1,seq2):
        return lift_to_fs(seq1+seq2)

    return Concatenate(word_1[:1], self(word_1[1:],word_2) ) + \
            Concatenate(word_2[:1], self(word_2[1:],word_1) )

@LiftFormalSum(FormalSum(0))
@lru_cache()
def shuffle_regularization_of_word(word, X = 0, Y = 0):
    r"""
    Description:

        Calculate shuffle regularization of input

    Input:

        word - sentence of "xy"

    Output:

        FormalSum of sentences of "xy", shuffle regularization of word

    Examples::
        sage: shuffle_regularization_of_word("yxyyx")
        yxyyx
        sage: shuffle_regularization_of_word( shuffle_product_of_word("x","yx") )
        0
        sage: shuffle_regularization_of_word( shuffle_product_of_word("y","yx") )
        0
        sage: X,Y = PolynomialRing(QQ, "tX,tY").gens()
        sage: shuffle_regularization_of_word("xy", X=X, Y=Y)
        -yx + tX*tY
        sage: shuffle_regularization_of_word("xxx", X=X, Y=Y)
        1/6*tX^3
    """
    assert all(c=="x" or c=="y" for c in word)
    l = 0
    r = len(word)
    while l < len(word) and word[l]=="x":
        l+=1
    while r > 0 and word[r-1]=="y":
        r -= 1
    if l==0 and r==len(word):
        return lift_to_fs(word)
    term = shuffle_product_of_word( shuffle_product_of_word(word[:l], word[l:r]), word[r:] )
    res = shuffle_regularization_of_word( lift_to_fs(word)-term, X=X, Y=Y )
    if X!=0 or Y!=0:
        nl = l
        nr = len(word) - r
        res += X**nl * Y**nr/factorial(nl) /factorial(nr) * lift_to_fs( word[l:r] )
    return res

def word_from_index(ks):
    return "".join("y"+"x"*(k-1) for k in ks)
def index_from_word(word):
    if not all(c=="x" or c=="y" for c in word):
        raise Exception(f'{word}')
    ret = []
    for c in word:
        if c=="x":
            ret[-1]+=1
        elif c=="y":
            ret.append(1)
    return tuple(ret)

@lru_cache()
def shuffle_regularization_of_index(ks):
    word = word_from_index(ks)
    reg_words = shuffle_regularization_of_word(word)
    #print(f'ks = {ks}, word = {word}, reg_words = {reg_words}')
    return FormalSum([(c,index_from_word(word))  for c,word in reg_words])

@LiftFormalSum(zero=multiple_zeta(2)-multiple_zeta(2))
@lru_cache()
def shuffle_regularized_multiple_zeta(ks):
    r"""
    Description:

        Calculate shuffle regularized multiple zeta values

    Input:

        ks - tuple of integers

    Output:

        multiple zeta

    Examples::
        sage: shuffle_regularized_multiple_zeta((1,3))==multiple_zeta(1,3)
        True

        sage: shuffle_regularized_multiple_zeta((1,1))
        0
    """
    return sum( c*multiple_zeta(*ls) for c,ls in shuffle_regularization_of_index(ks) )

@LiftFormalSum(zero=multiple_zeta(2)-multiple_zeta(2))
@lru_cache()
def shuffle_regularized_multiple_zeta_of_word(word, X = 0, Y=0):
    r"""
    Description:

        Calculate shuffle regularized multiple zeta values of given word

    Input:

        word - (usual or Formal sum of) string

    Output:

        multiple zeta

    Examples::
        sage: shuffle_regularized_multiple_zeta_of_word("yx")
        z2

        sage: X,Y = PolynomialRing(multiple_zeta(2).parent(), "X,Y").gens()
        sage: shuffle_regularized_multiple_zeta_of_word("xy", X=X, Y=Y)
        X*Y - z2

        sage: X,Y = PolynomialRing(multiple_zeta(2).parent(), "X,Y").gens()
        sage: shuffle_regularized_multiple_zeta_of_word("yxy", X=X, Y=Y)
        z2*Y - 2*z3

        sage: X,Y = PolynomialRing(multiple_zeta(2).parent(), "X,Y").gens()
        sage: shuffle_regularized_multiple_zeta_of_word("xxx", X=X, Y=Y)
        1/6*X^3

    """
    return sum( c*multiple_zeta(index_from_word(ls)) for c,ls in shuffle_regularization_of_word(word, X=X, Y=Y) )

@LiftFormalSum( zero=multiple_zeta(2)-multiple_zeta(2) )
@lru_cache()
def harmonic_regularized_multiple_zeta(ks, T = 0):
    r"""
    Description:

        Calculate harmonic regularized multiple zeta values

    Input:

        ks - tuple of integers

    Output:

        multiple zeta

    Examples::
        sage: harmonic_regularized_multiple_zeta((1,3))==multiple_zeta(1,3)
        True

        sage: harmonic_regularized_multiple_zeta( harmonic_product((1,),(3,4) ) )
        0

        sage: R = multiple_zeta(2).parent()
        sage: T = PolynomialRing(R, "T").gen(0)
        sage: harmonic_regularized_multiple_zeta( (2, 1), T = T )
        z2*T - 2*z3
    """
    return sum( c*multiple_zeta(*ls) for c,ls in HarmonicRegularization(ks, T=T) )

@LiftFormalSum( zero=multiple_zeta(2)-multiple_zeta(2) )
@lru_cache()
def harmonic_regularized_multiple_zeta_star(ks, T = 0):
    r"""
    Description:

        Calculate harmonic regularized multiple zeta star values

    Input:

        ks - tuple of integers

    Output:

        multiple zeta

    Examples::
        sage: harmonic_regularized_multiple_zeta_star((1,3)) == harmonic_regularized_multiple_zeta((1,3)) + harmonic_regularized_multiple_zeta((4,))
        True
    """
    return sum( c*harmonic_regularized_multiple_zeta(ls, T=T) for c,ls in star_index(ks) )

def regularized_multiple_zeta(ks, regularization):
    if regularization=="shuffle":
        return shuffle_regularized_multiple_zeta(ks)
    elif regularization=="harmonic":
        return harmonic_regularized_multiple_zeta(ks)
    else:
        assert False

@LiftFormalSum(0)
def t_adic_symmetric_multiple_zeta_at_degree(ks, degree, regularization):
    r"""
    Description:

        Calculate t-adic symmetric multiple zeta values for speicific degree

    Input:

        ks - tuple of integers, index
        degree - integer
        regularization - string, "shuffle" or "harmonic", regulazation method

    Output:

        zeta value, coefficient of t^degree in t-adic symmetric multiple zeta values at ks

    Examples::
        sage: regularization = "harmonic"
        sage: ks = (3,4)
        sage: ls = (4,5)
        sage: a0 = t_adic_symmetric_multiple_zeta_at_degree(ks, 0, regularization)
        sage: a1 = t_adic_symmetric_multiple_zeta_at_degree(ks, 1, regularization)
        sage: b0 = t_adic_symmetric_multiple_zeta_at_degree(ls, 0, regularization)
        sage: b1 = t_adic_symmetric_multiple_zeta_at_degree(ls, 1, regularization)
        sage: c0 = t_adic_symmetric_multiple_zeta_at_degree(harmonic_product(ks,ls), 0, regularization)
        sage: c1 = t_adic_symmetric_multiple_zeta_at_degree(harmonic_product(ks,ls), 1, regularization)
        sage: a0*b0-c0
        0
        sage: a0*b1+b0*a1-c1
        0

    """
    reg_mzv = lambda ks: regularized_multiple_zeta(ks,regularization)
    def componentwise_sum(ks,ls):
        assert len(ks)==len(ls)
        return tuple(k+l for k,l in zip(ks,ls))
    def b(ks,ls):
        #print(f'ks = {ks}, ls = {ls}')
        return mul(binomial(k+l-1,l) for k,l in zip(ks,ls))
    def mzv_sub(ks,l):
        return (-1)**l*sum( b(ks,ls) * reg_mzv(componentwise_sum(ks,ls)) for ls in generate_all_index_admit_zero(weight = l, depth = len(ks)) )
    return sum( reg_mzv(ks[:i]) * mzv_sub(ks[i:][::-1],degree) * (-1)**(sum(ks[i:])+degree)  for i in range(0, len(ks)+1))

def star_index(ks):
    r"""
    Description:

        Calculate star index of inputs

    Input:

        ks - tuple of integers, index

    Output:

        FormalSum of tuple of integers, sum of all index which can be obtained by changing some commas of ks to plus.

    Examples::
        sage: ks = (3,4)
        sage: expected = lift_to_fs((3,4)) + lift_to_fs((7,))
        sage: star_index(ks)==expected
        True

    """
    def rec(ls):
        if len(ls)<=1:
            return [ls]
        return [ls[:1]+seq for seq in rec(ls[1:])] + rec((ls[0]+ls[1],) + ls[2:])
    ks = tuple(ks)
    return FormalSum([(1,seq) for seq in rec(ks)])
    pass

def multiple_zeta_star(ks):
    r"""
    Description:

        Calculate multiple zeta star value of inputs

    Input:

        ks - tuple of integers, index

    Output:

        multiple zeta, multiple zeta star value of input.

    Examples::
        sage: multiple_zeta_star((3,5)) == multiple_zeta((3,5)) + multiple_zeta((8,))
        True
        sage: multiple_zeta_star((1,1,1,2)) == 4*multiple_zeta((5,))
        True

    """
    return sum(c*multiple_zeta(ls) for c,ls in star_index(ks))

def polynomial_multiple_zeta(ks, x = None, y = None, T = None):
    r"""
    Description:

        Calculate (harmonic regularized) polynomial multiple zeta value f inputs
        see https://arxiv.org/pdf/1808.06745.pdf for detail.

    Input:

        ks - tuple of integers, index

    Output:

        x,y,T polynomial of multiple zetas, polynomial multiple zeta value of inputs of input.

    Examples::
        sage: ks = (3,4,5)
        sage: polynomial_multiple_zeta(ks, x=1, y=0) == multiple_zeta(ks)
        True
    """
    default_x,default_y,default_T = PolynomialRing(multiple_zeta(2).parent(), "x,y,T").gens()
    if x==None:
        x = default_x
    if y==None:
        y = default_y
    if T==None:
        T = default_T

    r = len(ks)
    return sum(x**sum(ks[:i])*y**sum(ks[i:])*harmonic_regularized_multiple_zeta(ks[:i],T=T)*harmonic_regularized_multiple_zeta(ks[i:][::-1],T=T) for i in range(r+1))

def polynomial_multiple_zeta_star(ks, x = None, y = None, T = None):
    r"""
    Description:

        Calculate (harmonic regularized) polynomial multiple zeta value f inputs
        see https://arxiv.org/pdf/1808.06745.pdf for detail.

    Input:

        ks - tuple of integers, index

    Output:

        x,y,T polynomial of multiple zetas, polynomial multiple zeta value of inputs of input.

    Examples::
        sage: ks = (3,4,5)
        sage: polynomial_multiple_zeta_star(ks, x=1, y=0) == multiple_zeta_star(ks)
        True
    """
    default_x,default_y,default_T = PolynomialRing(multiple_zeta(2).parent(), "x,y,T").gens()
    if x==None:
        x = default_x
    if y==None:
        y = default_y
    if T==None:
        T = default_T

    r = len(ks)
    return sum(x**sum(ks[:i])*y**sum(ks[i:])*harmonic_regularized_multiple_zeta_star(ks[:i],T=T)*harmonic_regularized_multiple_zeta_star(ks[i:][::-1],T=T) for i in range(r+1))



def Gamma1(A):
    r"""
    Description:

        Calculate Gamma_1(A)

    Input:

        A - varialbe in formal power series ring

    Output:

        value of Gamma_1 function

    Examples::
        sage: R = multiple_zeta(2).parent()
        sage: P = PowerSeriesRing(R, "A", default_prec = 5)
        sage: A = P.gen(0)
        sage: Gamma1(A)
        1 + 1/2*z2*A^2 - 1/3*z3*A^3 + 9/40*z2^2*A^4 + O(A^5)

    """
    prec = A.parent().default_prec()
    ret = 0
    for k in range(2,prec):
        ret += multiple_zeta(k)/k*(-A)**k
    return exp(ret)

@LiftFormalSum(FormalSum(0))
@lru_cache()
def OhnoSum_word(m, word):
    r"""
    Description:

        Calculate Ohno sum of word

    Input:

        m - Integer
        word - sentence of "xy"

    Output:

        FormalSum of sentences of "xy", m-th Ohno sum of word

    Examples::
        sage: OhnoSum_word(2, "xyxyxx")
        xyxxxyxx + xyxxyxxx + xyxyxxxx
    """
    assert all(c in ["x","y"] for  c in word)
    ks = [ len(seq) for seq in  word.split("y")]
    ret = FormalSum([])
    for es in  generate_all_index_admit_zero(weight = m, depth = len(ks)-1):
        ls = [k+e for k,e in zip(ks,(0,)+es)]
        ret += lift_to_fs( "y".join("x"*int(l) for l in ls) )
    return ret



def mono_dual(ks):
    assert type(ks)==list
    assert ks[-1]>=2
    ret = []
    for k in ks[::-1]:
        for _ in range(k-1):
            ret.append(1)
        ret[-1]+=1
    return ret
@LiftFormalSum(FormalSum(0) )
def dual(ks):
    type(ks)==list
    return FormalSum([(1,mono_dual(ks))])


def all_partitions(n, length):
    ret = []
    def rec(seq):
        if len(seq)==length:
            if sum(seq)==n:ret.append(seq)
            return
        for i in range(1,n-sum(seq)+1):
            if len(seq)>0 and i>min(seq):break
            rec(seq+[i])
    rec([])
    return ret

def get_rank_for_polynomials(polynomials):
    r"""
    Description:

        Calculate the dimension of vector space generated by polynomials in input

    Input:

        list or tuple of polynomials

    Output:

        Integer, the dimension of vector space generated by polynomials in input

    Examples::
        sage: mzv_dim = lambda w: get_rank_for_polynomials([multiple_zeta(ks) for ks in generate_all_index(w) if ks[-1]!=1])
        sage: [mzv_dim(w) for w in [1,2,3,4,5,6,7,8,9,10,11,12]]
        [0, 1, 1, 1, 2, 2, 3, 4, 5, 7, 9, 12]

    """
    from sage.all import matrix
    ind_from_coefficient = {}
    for i,pol in enumerate(polynomials):
        for key in pol.dict():
            if key not in ind_from_coefficient:
                ind_from_coefficient[key] = len(ind_from_coefficient)
    m = []
    for pol in polynomials:
        vec = [0] * len(ind_from_coefficient)
        for key,val in pol.dict().items():
            ind = ind_from_coefficient[key]
            vec[ind] += val
        m.append(vec)

    return matrix(m).rank()

class Timer:
    import time
    def __init__(self):
        self.dict_time_record = {}
        self.start_time_stack = []
        pass

    def start(self, message):
        if type(message) != str:
            print("Error at Timer.start()")
            print("message = ", message)
            print("type(message) = ", type(message))
            print("message should be str !")
            raise ""
        self.start_time_stack.append( (message, time.time()) )

    def stop(self):
        if len(self.start_time_stack)==0:
            print("Error at Timer.stop()")
            print("There are no stacks")
        message, prev_time = self.start_time_stack.pop()
        if message not in self.dict_time_record:
            self.dict_time_record[message] = 0.0
        self.dict_time_record[message] += time.time() - prev_time

    def result(self):
        if len(self.start_time_stack)>0:
            print("Timer: BROKEN STATE")
            print("stack = ", self.start_time_stack)
        print("Timer result ----------------")
        max_l = max( len(message) for message in self.dict_time_record )
        for message, time_used in self.dict_time_record.items():
            print(message, "-"*( 3+max_l - len(message) )+" ", time_used)
        print("-----------------------------")
