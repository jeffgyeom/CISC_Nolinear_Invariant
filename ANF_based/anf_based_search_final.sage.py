
# This file was *autogenerated* from the file ./anf_based_search_final.sage
from sage.all_cmdline import *   # import sage library

_sage_const_3 = Integer(3); _sage_const_2 = Integer(2); _sage_const_1 = Integer(1); _sage_const_0 = Integer(0); _sage_const_7 = Integer(7); _sage_const_6 = Integer(6); _sage_const_5 = Integer(5); _sage_const_4 = Integer(4); _sage_const_0x1 = Integer(0x1); _sage_const_8 = Integer(8); _sage_const_16 = Integer(16); _sage_const_20 = Integer(20)#!/usr/bin/env sage
#this code supports python2.x only
from sage.all import *
from sage.crypto.boolean_function import BooleanFunction
from sage.crypto.sbox import SBox
import copy
import sys
sys.path.append('../sboxes_info/')
from sboxes import *

#Analysis Threshold
ANALYSIS_BIT_RANGE = _sage_const_20 

#General Information
ALG_NAME = ""
S_BOX  = []
S_BOX_CARDINALITY = _sage_const_0 
S_BOX_BIT_SIZE = _sage_const_0 
S_BOX_BOOLEANS  = []


def set_sbox():
    for i in range(len(SBOXES)):
        print ("%s" % (SBOXES[i][_sage_const_0 ]))
    chosen = raw_input("> Which S-Box?(e.g., PRESENT):")
    
    global ALG_NAME
    global S_BOX
    global S_BOX_CARDINALITY
    global S_BOX_BIT_SIZE

    chosen_idx = -_sage_const_1 
    for i in range(len(SBOXES)):
        if (SBOXES[i][_sage_const_0 ] == chosen) or (SBOXES[i][_sage_const_0 ] == chosen.upper()):
            chosen_idx = i
            ALG_NAME = SBOXES[i][_sage_const_0 ]
            S_BOX = SBOXES[i][_sage_const_1 ]
            S_BOX_CARDINALITY = len(SBOXES[i][_sage_const_1 ])
            S_BOX_BIT_SIZE = S_BOX_CARDINALITY.bit_length() - _sage_const_1 

    if chosen_idx == -_sage_const_1 :
        print ("error : the S-Box(%s) does not exist" %chosen.upper())


# S-Box(x3, x2, x1, x0) = 
# {f3(x3, x2, x1, x0), 
#  f2(x3, x2, x1, x0), 
#  f1(x3, x2, x1, x0), 
#  f0(x3, x2, x1, x0)}
def get_sbox_anf():

    global S_BOX_BOOLEANS

    S_BOX_BOOLEANS = range(S_BOX_BIT_SIZE)

    for i in range(S_BOX_BIT_SIZE):
        S = SBox(S_BOX)
        S_BOX_BOOLEANS[i] = S.component_function((_sage_const_0x1 <<i))



def is_nonlinear_invariant(S_Box, nonlinear_invariant):
    tt = nonlinear_invariant.truth_table(format='int')
    init = tt[_sage_const_0 ] ^ tt[S_Box[_sage_const_0 ]]
    flag = _sage_const_0 
    for x in range(_sage_const_1 ,len(S_Box)):
        if tt[x] ^ tt[S_Box[x]] != init:
            flag = _sage_const_1 
    if flag == _sage_const_1 :
        return False
    else:
        return True


#Set S-Box
set_sbox()

#get each ouput boolean mn functions
get_sbox_anf()

#Set Ring
MONOMIALS = [] #Monomias are the basis of the NONLINEAR_INVARIANT_MATRIX
if S_BOX_BIT_SIZE == _sage_const_3 :
    R = BooleanPolynomialRing(_sage_const_3 , names=('x2', 'x1', 'x0',)); (x2, x1, x0,) = R._first_ngens(3)
    MONOMIALS = monomials([x2,x1,x0],[_sage_const_2 ,_sage_const_2 ,_sage_const_2 ])
elif S_BOX_BIT_SIZE == _sage_const_4 :
    R = BooleanPolynomialRing(_sage_const_4 , names=('x3', 'x2', 'x1', 'x0',)); (x3, x2, x1, x0,) = R._first_ngens(4)
    MONOMIALS = monomials([x3,x2,x1,x0],[_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ])
elif S_BOX_BIT_SIZE == _sage_const_5 :
    R = BooleanPolynomialRing(_sage_const_5 , names=('x4', 'x3', 'x2', 'x1', 'x0',)); (x4, x3, x2, x1, x0,) = R._first_ngens(5)
    MONOMIALS = monomials([x4,x3,x2,x1,x0],[_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ])
elif S_BOX_BIT_SIZE == _sage_const_6 :
    R = BooleanPolynomialRing(_sage_const_6 , names=('x5', 'x4', 'x3', 'x2', 'x1', 'x0',)); (x5, x4, x3, x2, x1, x0,) = R._first_ngens(6)
    MONOMIALS = monomials([x5,x4,x3,x2,x1,x0],[_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ])
elif S_BOX_BIT_SIZE == _sage_const_7 :
    R = BooleanPolynomialRing(_sage_const_7 , names=('x6', 'x5', 'x4', 'x3', 'x2', 'x1', 'x0',)); (x6, x5, x4, x3, x2, x1, x0,) = R._first_ngens(7)
    MONOMIALS = monomials([x6,x5,x4,x3,x2,x1,x0],[_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ])
elif S_BOX_BIT_SIZE == _sage_const_8 :
    R = BooleanPolynomialRing(_sage_const_8 , names=('x7', 'x6', 'x5', 'x4', 'x3', 'x2', 'x1', 'x0',)); (x7, x6, x5, x4, x3, x2, x1, x0,) = R._first_ngens(8)
    MONOMIALS = monomials([x7,x6,x5,x4,x3,x2,x1,x0],[_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ])
elif S_BOX_BIT_SIZE == _sage_const_16 :
    R = BooleanPolynomialRing(_sage_const_16 , names=('x15', 'x14', 'x13', 'x12', 'x11', 'x10', 'x9', 'x8', 'x7', 'x6', 'x5', 'x4', 'x3', 'x2', 'x1', 'x0',)); (x15, x14, x13, x12, x11, x10, x9, x8, x7, x6, x5, x4, x3, x2, x1, x0,) = R._first_ngens(16)
    MONOMIALS = monomials([x15,x14,x13,x12,x11,x10,x9,x8,x7,x6,x5,x4,x3,x2,x1,x0],[_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ,_sage_const_2 ])
else:
    print("The bit size of the S-box is not supported")
    exit

NUM_MONOMIALS = int(_sage_const_2 **S_BOX_BIT_SIZE)
MONOMIALS_ANF_STR = range(NUM_MONOMIALS)

for i in range(NUM_MONOMIALS):
    MONOMIALS[i] = BooleanFunction(MONOMIALS[i])
    MONOMIALS_ANF_STR[i] = str(MONOMIALS[i].algebraic_normal_form())


NONLINEAR_INVARIANT_MATRIX = matrix(GF(_sage_const_2 ), NUM_MONOMIALS)
#compute NONLINEAR_INVARIANT_MATRIX
for row in range(NUM_MONOMIALS):
    for col in range(NUM_MONOMIALS):
        NONLINEAR_INVARIANT_MATRIX[row,col] = _sage_const_0 

for mono_idx in range(NUM_MONOMIALS):
    mono_sbox = BooleanFunction(x0**(_sage_const_0 )) # here "1"
    for var_idx in range(S_BOX_BIT_SIZE):
        if "x%d"%var_idx in MONOMIALS_ANF_STR[mono_idx]:
            mono_sbox = mono_sbox * S_BOX_BOOLEANS[var_idx]
    mono_plus_mono_sbox = MONOMIALS[mono_idx] + mono_sbox
    mono_plus_mono_sbox_anf_str = str(mono_plus_mono_sbox.algebraic_normal_form())
    mono_plus_mono_sbox_anf_str = mono_plus_mono_sbox_anf_str.split(' + ')
    for cur_mono in mono_plus_mono_sbox_anf_str:
        if cur_mono in MONOMIALS_ANF_STR:
            basis_idx = MONOMIALS_ANF_STR.index(cur_mono)
            NONLINEAR_INVARIANT_MATRIX[mono_idx, basis_idx] = _sage_const_1 

print("The %dX%d matrix"%(NONLINEAR_INVARIANT_MATRIX.nrows(),NONLINEAR_INVARIANT_MATRIX.ncols()))
#start computing

#check if the left range of the matrix includes {1,0,...}
_1_vector = range(NUM_MONOMIALS)
for i in range(NUM_MONOMIALS):
    _1_vector[i] =_sage_const_0 
_1_idx = MONOMIALS_ANF_STR.index("1")
_1_vector[_1_idx] = _sage_const_1 
_1_vector = vector(_1_vector)

left_1_vector_sole = vector(range(NUM_MONOMIALS))
left_1_vector_solvable = _sage_const_1 
try:
    left_1_vector_sole = NONLINEAR_INVARIANT_MATRIX.solve_left(_1_vector)
except:
    left_1_vector_solvable = _sage_const_0 
if left_1_vector_solvable == _sage_const_1 :
   left_1_vector_sole = NONLINEAR_INVARIANT_MATRIX.solve_left(_1_vector)


ker = NONLINEAR_INVARIANT_MATRIX.left_kernel()
ker_dim = ker.dimension()

ker_basis_list = ker.basis()

for i in range(len(ker_basis_list)):
    K = BooleanFunction(x0 + x0) # here "0"
    for j in range(NUM_MONOMIALS):
        if ker_basis_list[i][j] == _sage_const_1 :
            K = K + MONOMIALS[j]
    #check if it is a nonlinear invariant
    if is_nonlinear_invariant(S_BOX, K) is not True:
        print("Warning! "), (K.algebraic_normal_form()), ("is not a nonlinear invariant but it is got from the matrix")

if left_1_vector_solvable == _sage_const_1 :
    K = BooleanFunction(x0 + x0) # here "0"
    for j in range(NUM_MONOMIALS):
        if left_1_vector_sole[j] == _sage_const_1 :
            K = K + MONOMIALS[j]
    #check if it is a nonlinear invariant
    if is_nonlinear_invariant(S_BOX, K) is not True:
        print("Warning! "), (K.algebraic_normal_form()), ("is not a nonlinear invariant but it is got from the matrix")


#S-Box(x(n-1), x(n-2), ..., x0)
NUM_NON_INVARIANT = _sage_const_0 
NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = _sage_const_0 
NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = _sage_const_0 

if left_1_vector_solvable:
    NUM_NON_INVARIANT = (_sage_const_2 **ker_dim)*_sage_const_2 
else:
    NUM_NON_INVARIANT = (_sage_const_2 **ker_dim)

print ("== Nonlinear Invariants Info of %s" %ALG_NAME)
if left_1_vector_solvable:
    print ("{1,0,...,0} has a left solution.")
    print ("Therefore, nonlinear invariants g such that g(x) + g(sbox(x)) = 1 are included.")
else:
    print ("{1,0,...,0} does *NOT* have a left solution.")
    print ("Therefore, nonlinear invariants g such that g(x) + g(sbox(x)) = 1 are *NOT* included.")
print ("# of Nonlinear Invariants : %d" % NUM_NON_INVARIANT)

#From here : Optional up to # of nonlinear invariants
if ker_dim < ANALYSIS_BIT_RANGE:
    ker_list = ker.list()
    for i in range(len(ker_list)):
        K = BooleanFunction(x0 + x0) # here "0"
        for j in range(NUM_MONOMIALS):
            if ker_list[i][j] == _sage_const_1 :
                K = K + MONOMIALS[j]

        #check if it has the linear structure
        if K.has_linear_structure():
            NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE + _sage_const_1 
            #check if it is balanced
            if K.is_balanced():
                NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE +_sage_const_1 

        if left_1_vector_solvable == _sage_const_1 :
            for j in range(NUM_MONOMIALS):
                if left_1_vector_sole[j] ==_sage_const_1 :
                    K = K + MONOMIALS[j]
            #check if it has the linear structure
            if K.has_linear_structure():
                NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE + _sage_const_1 
                #check if it is balanced
                if K.is_balanced():
                    NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE +_sage_const_1 
    print ("# of Nonlinear Invariants with Linear Structure : %d" % NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE)
    print ("# of Balanced Nonlinear Invariants with Linear Structure : %d" % NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE)
else:
    print("# of nonlinear invariants is too large to analyze.")

