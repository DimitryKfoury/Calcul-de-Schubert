# initialisation yields combinatorial data related to a root system.
# parameters are: the type of the root system, the rank, and boolean variable affine which tells if we want an affine Weyl group of the usual finite one.
# initialisation creates and computes a series of global variables:
# W is the corresponding affine Weyl group.
# s is an array: s[i] is the i-th reflection in the Weyl group W.
# P is a polynomial ring, it represents the T-equivariant cohomology of a point. Q is its fraction field.
# a is the array of generators of P (a[i]=equivariant class of the simple root alpha_i).
# r is the rank
def initialisation(type,rank,affine):
    global W,s,P,Q,a,r,S,is_affine
    if affine==true:
       W = WeylGroup(RootSystem([type,rank,1]).root_lattice(),prefix="s")
    else:
       W = WeylGroup(RootSystem([type,rank]).root_lattice(),prefix="s")
    s = W.simple_reflections()

    P = PolynomialRing(ZZ,rank+1,"a")
    Q=Frac(P)
    aa = P.gens()
    a=[aa[0]]
    r = rank
    is_affine = affine

    for i in range(1,r+1):
        a=a+[aa[i]]


# A HeckeMonomial is an element of the form f delta_w, with f in P and w in the affine Weyl group.
# HeckeMonomials are sum to create HeckePolynomials.
class HeckeMonomial:
    def __init__(self,w,f):
        self._w=w
        self._f=f
    def __repr__(self):
        return "( %s : %s )"%(self._w,self._f)
    def  w(self):
        return self._w
    def  f(self):
        return self._f
    def __mul__(self,m2):
        return MonomialProduct(self,m2)



# A HeckePolynomial is by construction a sum of HeckeMonomials.
class HeckePolynomial:
  def __init__(self,list):
      self._list=list
  def __repr__(self):
      return "(%s)" %(self._list)
  def  m(self):
      return self._m



#MonomialProduct function takes two Heckemonomials hm1=delta_{w1} f1 and hm2=delta_{w2} f2,
#and returns the product in the NilHeck ring: hm1 hm2= delta_{w1w2} w2^{-1}(f1) f2.
def MonomialProduct(hm1,hm2):
    global r,is_affine
    w1=hm1.w()
    w2=hm2.w()
    Matrix_form_of_w2=w2.matrix()
    Inverse_Matrix_of_w2=Matrix_form_of_w2.inverse()
    f1=hm1.f()
    f2=hm2.f()
    b = [0]
    if is_affine == True:
        for i in range(0,len(s)+0):
            b=b+[0]
        for j in range(0,len(s)+0):
            for k in range(0,len(s)+0):
                b[j]=b[j]+Inverse_Matrix_of_w2[k-0,j-0]*a[k]

        return HeckeMonomial (w1*w2,f1.subs({a[i]:b[i] for i in range(len(s)+0)})*f2)
    else:
        for i in range(1,len(s)+1):
            b=b+[0]
        for j in range(1,len(s)+1):
            for k in range(1,len(s)+1):
                b[j]=b[j]+Inverse_Matrix_of_w2[k-1,j-1]*a[k]

        return HeckeMonomial (w1*w2,f1.subs({a[i]:b[i] for i in range(len(s)+1)})*f2)






#The r function takes a List b which represents a reduced word, and an integer m less than the length of b.
#The r function then returns the root s_{b[0]}s_{b[1]}...s_{b[m-1]}(a[m]).
#This function represents the mth positive root r_b(m) defined by Sarah Billey.
def r(b,m):
    r=W.one()
    for i in range(m-1):
        r=r*s[b[i]]
    r1=r**(-1)
    ab=a[b[m-1]]
    rbj=MonomialProduct(HeckeMonomial(W.one(),ab),HeckeMonomial(r1,a[1]/a[1])).f()

    return rbj


# function suite_suivante uses the global variable L, which represents an increasing sequence of k integers
# between 1 and l. It yields the next such sequence in lexicographic order. For example, let k=2 and l=4.
# If L=[1,4] then suite_suivante will return [2,3], and if L=[2,3], then suite_suivante will return [2,4].
# When L is the last sequence, then suite_suivante will return a sequence with L[0]=0, which means that
# all the sequences have been dealt with.
def suite_suivante(k,l):
    global Z
    K=k
    Z=L
    while (K>0):
        if Z[K-1]<l-k+K:     # It is possible to increase the value of Z[K-1]
            for i in range(k-K+1):
                Z[k-1-i]=Z[K-1]+k-K-i+1  # Set the next values Z[K], Z[K+1], etc, to be the minimal ones, increasing by exactly one at each step.
            K=-1
        else:       # It is not possible to increase the value of Z[K-1], so lower K to increase some value before K-1.
            K=K-1
            if K==0:
                Z[0]=0
    return Z


# The lex function takes two integers k<l, and generates lists L of length k containing all possible increasing combinations of integers from 1 to l.
def lex(k,l):
    global LL
    LL=[]
    global L
    L=[]
    for i in range (k):
        L=L+[i+1]
    while L[0]>0:
        LL=LL+[L[:k]]
        L=suite_suivante(k,l)



def Lex(l):
    lexi=[]
    for i in range(1,l):
        lex(i,l)
        lexi=lexi+LL
    return lexi




#The xi function takes two elements, v and w, of the Weyl group W, and returns the following: Let b=b[1]...b[p] be a reduced word of w.
#If v is not less than w (in the Bruhat order), it will return 0.
#If v is less than w (in the Bruhat order), it will compute the sum, over all reduced words of v of the form b[i1]...b[ik], of the products r(b,i1)....r(b,ik).
#This function represents the function \xi(v,w) defined by Sarah billey (cf. Lemme 4.1). She also proves in her article that this function is in fact independent of the choice of the reduced word b.
#Indeed, this is the value of the equivariant cohomology class \xi^v at the fixed point w.
def xi(v,w):
    Subwords_of_w_of_length_v=[] #This List will contain all subwords of a given reduced word of w, which are of the same length as v.
    length_of_w=len(w.reduced_word())
    length_of_v=len(v.reduced_word())
    Reduced_word_of_w=w.reduced_word()
    Set_of_reduced_words_of_v=v.reduced_words()
    product_1=P.one()
    product_2=P.one()
    result=P.zero()
    lex(length_of_v,length_of_w)
    for i in range (len(LL)):
        Subwords_of_w_of_length_v=Subwords_of_w_of_length_v+[[]]
    if v.bruhat_le(w):
        for i in range (len(LL)):
            for j in range (length_of_v):
                Subwords_of_w_of_length_v[i]=Subwords_of_w_of_length_v[i]+[Reduced_word_of_w[LL[i][j]-1]]

        for i in range(len(Subwords_of_w_of_length_v)):
            if Subwords_of_w_of_length_v[i] in Set_of_reduced_words_of_v:
                for j in range(len(Subwords_of_w_of_length_v[i])):
                    product_1=product_1* r(Reduced_word_of_w,LL[i][j])
                    product_2=product_2*product_1
                    product_1=P.one()
                result=result+product_2
                product_2=P.one()

    return result





#The pi function takes an element v (of reduced word b=[b[0],...,b[p-1]]) of the Weyl group and computes the product r(b,1)*r(b,2)*...*r(b,p).
def pi(v):
    Pi=a[1]/a[1]
    b=v.reduced_word()
    p=len(b)
    for i in range (p):
        Pi=Pi*r(b,i+1)

    return Pi

#The p function takes three elements u,v and w of the Weyl group, and computes the structure constantes p_{u,v}^w of Cohomology algebra of the affine Grassmannian.
#More precisely, using Sarah Billey's method, this function calculates these constants by induction on the length of w.
def p(u,v,w):
    lexi=Lex(len(w.reduced_word()))
    sigma=0
    for t in W.bruhat_interval(u,w):
        if v.bruhat_le(t) and t.length()<w.length():
            sigma=sigma+p(u,v,t)*xi(t,w)

    return (1/pi(w))*(xi(u,w)*xi(v,w)-sigma)

#The elements_of_length function taks an integer l, and returns a list containing all elements of the Weyl group of length l.
def elements_of_length(l):
    List=[]
    for w in W.elements_of_length(l):
        List=List+[w]
    return List

#The Schubert_Product function takes two elements u and v of the Weyl group, and returns the product xi^u xi^v,
#in function of elements xi^w such that p(u,v,w) is different than 0.
#More precisely it will calculate the coefficient of each Schubert class xi^w above.
def Schubert_Product(u,v):
    Reduced_word_of_u=u.reduced_word()
    Reduced_word_of_v=v.reduced_word()
    len_u_plus_len_v=len(Reduced_word_of_u)+len(Reduced_word_of_v)
    elements_of_length_sum_of_length=elements_of_length(len_u_plus_len_v)
    length_of_List=len(elements_of_length_sum_of_length)
    for i in range (length_of_List):
        if v.bruhat_le(elements_of_length_sum_of_length[i]) and u.bruhat_le(elements_of_length_sum_of_length[i]) and p(u,v,elements_of_length_sum_of_length[i])!=0:
            print (elements_of_length_sum_of_length[i],":",p(u,v,elements_of_length_sum_of_length[i]))
