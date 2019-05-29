#!/usr/bin/env sage
#this code supports python2.x only
from sage.all import *
from sage.crypto.boolean_function import BooleanFunction
from sage.crypto.sbox import SBox
import copy
import sys
sys.path.append('../sboxes_info/')
from sboxes import *

VERVOSE = 0

#Information
ALG_NAME = ""
S_BOX  = []
S_BOX_CARDINALITY = 0
S_BOX_BIT_SIZE = 0
S_BOX_BOOLEANS  = []


def set_sbox():
    for i in range(len(SBOXES)):
        print ("%s" % (SBOXES[i][0]))
    chosen = raw_input("> Which S-Box?(e.g., PRESENT):")
    
    global ALG_NAME
    global S_BOX
    global S_BOX_CARDINALITY
    global S_BOX_BIT_SIZE

    chosen_idx = -1
    for i in range(len(SBOXES)):
        if (SBOXES[i][0] == chosen) or (SBOXES[i][0] == chosen.upper()):
            chosen_idx = i
            ALG_NAME = SBOXES[i][0]
            S_BOX = SBOXES[i][1]
            S_BOX_CARDINALITY = len(SBOXES[i][1])
            S_BOX_BIT_SIZE = S_BOX_CARDINALITY.bit_length() - 1

    if chosen_idx == -1:
        print ("error : the S-Box(%s) does not exist" %chosen.upper())


# S-Box(x3, x2, x1, x0) = 
# {f3(x3, x2, x1, x0), 
#  f2(x3, x2, x1, x0), 
#  f1(x3, x2, x1, x0), 
#  f0(x3, x2, x1, x0)}
def get_sbox_anf():

    global S_BOX_BOOLEANS

    S_BOX_BOOLEANS = range(S_BOX_BIT_SIZE)
    
    if VERVOSE == 1:
        print ("=======  S-Box ========")
        print ("S-Box(x(n-1), x(n-2), ..., x0 ) = {f(n-1)(x(n-1), x(n-2), ..., x0), f(n-2)(...), ..., f0}")

    for i in range(S_BOX_BIT_SIZE):
        S = SBox(S_BOX)
        S_BOX_BOOLEANS[i] = S.component_function((0x1<<i))
        if VERVOSE == 1:
            print ("f%d = "%i),(S_BOX_BOOLEANS[i].algebraic_normal_form())



def is_nonlinear_invariant(S_Box, nonlinear_invariant):
    tt = nonlinear_invariant.truth_table(format='int')
    init = tt[0] ^^ tt[S_Box[0]]
    flag = 0
    for x in range(1,len(S_Box)):
        if tt[x] ^^ tt[S_Box[x]] != init:
            flag = 1
    if flag == 1:
        return False
    else:
        return True


#Setting S-Box
set_sbox()

#get each ouput boolean mn functions
get_sbox_anf()

MONOMIALS = [] #Monomias are the basis of the NONLINEAR_INVARIANT_MATRIX
#RING

if S_BOX_BIT_SIZE == 3:
    R.<x2,x1,x0>=BooleanPolynomialRing(3)
    MONOMIALS = monomials([x2,x1,x0],[2,2,2])
elif S_BOX_BIT_SIZE == 4:
    R.<x3,x2,x1,x0>=BooleanPolynomialRing(4)
    MONOMIALS = monomials([x3,x2,x1,x0],[2,2,2,2])
elif S_BOX_BIT_SIZE == 5:
    R.<x4,x3,x2,x1,x0>=BooleanPolynomialRing(5)
    MONOMIALS = monomials([x4,x3,x2,x1,x0],[2,2,2,2,2])
elif S_BOX_BIT_SIZE == 6:
    R.<x5,x4,x3,x2,x1,x0>=BooleanPolynomialRing(6)
    MONOMIALS = monomials([x5,x4,x3,x2,x1,x0],[2,2,2,2,2,2])
elif S_BOX_BIT_SIZE == 7:
    R.<x6,x5,x4,x3,x2,x1,x0>=BooleanPolynomialRing(7)
    MONOMIALS = monomials([x6,x5,x4,x3,x2,x1,x0],[2,2,2,2,2,2,2])
elif S_BOX_BIT_SIZE == 8:
    R.<x7,x6,x5,x4,x3,x2,x1,x0>=BooleanPolynomialRing(8)
    MONOMIALS = monomials([x7,x6,x5,x4,x3,x2,x1,x0],[2,2,2,2,2,2,2,2])
else:
    print("The bit size of the S-box is not supported")
    exit

NUM_MONOMIALS = int(2**S_BOX_BIT_SIZE)
MONOMIALS_ANF_STR = range(NUM_MONOMIALS)

for i in range(NUM_MONOMIALS):
    MONOMIALS[i] = BooleanFunction(MONOMIALS[i])
    MONOMIALS_ANF_STR[i] = str(MONOMIALS[i].algebraic_normal_form())


NONLINEAR_INVARIANT_MATRIX = matrix(GF(2), NUM_MONOMIALS)
#compute NONLINEAR_INVARIANT_MATRIX
for row in range(NUM_MONOMIALS):
    for col in range(NUM_MONOMIALS):
        NONLINEAR_INVARIANT_MATRIX[row,col] = 0

for mono_idx in range(NUM_MONOMIALS):
    mono_sbox = BooleanFunction(x0^(0)) # here "1"
    for var_idx in range(S_BOX_BIT_SIZE):
        if "x%d"%var_idx in MONOMIALS_ANF_STR[mono_idx]:
            mono_sbox = mono_sbox * S_BOX_BOOLEANS[var_idx]
    mono_plus_mono_sbox = MONOMIALS[mono_idx] + mono_sbox
    mono_plus_mono_sbox_anf_str = str(mono_plus_mono_sbox.algebraic_normal_form())
    mono_plus_mono_sbox_anf_str = mono_plus_mono_sbox_anf_str.split(' + ')
    for cur_mono in mono_plus_mono_sbox_anf_str:
        if cur_mono in MONOMIALS_ANF_STR:
            basis_idx = MONOMIALS_ANF_STR.index(cur_mono)
            NONLINEAR_INVARIANT_MATRIX[mono_idx, basis_idx] = 1

if VERVOSE == 1:
    print ("======= Nonlinear Invariant Matrix ========")
    print("= Basis")
    for i in range(len(MONOMIALS)):
        print(str(MONOMIALS[i].algebraic_normal_form()) + ", "),
    print("")
    print(NONLINEAR_INVARIANT_MATRIX)   


#check if the left range of the matrix includes {1,0,...}
_1_vector = range(NUM_MONOMIALS)
for i in range(NUM_MONOMIALS):
    _1_vector[i] =0
_1_idx = MONOMIALS_ANF_STR.index("1")
_1_vector[_1_idx] = 1
_1_vector = vector(_1_vector)

left_1_vector_sole = vector(range(NUM_MONOMIALS))
left_1_vector_solvable = 1
try:
    left_1_vector_sole = NONLINEAR_INVARIANT_MATRIX.solve_left(_1_vector)
except:
    left_1_vector_solvable = 0
if left_1_vector_solvable == 1:
   left_1_vector_sole = NONLINEAR_INVARIANT_MATRIX.solve_left(_1_vector)


ker = NONLINEAR_INVARIANT_MATRIX.left_kernel()
ker_dim = ker.dimension()
NUM_NON_INVARIANT = 0
NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = 0
NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = 0

if left_1_vector_solvable:
    NUM_NON_INVARIANT = (2**ker_dim)*2
else:
    NUM_NON_INVARIANT = (2**ker_dim)

ker_basis_list = ker.basis()

for i in range(len(ker_basis_list)):
    K = BooleanFunction(x0 + x0) # here "0"
    for j in range(NUM_MONOMIALS):
        if ker_basis_list[i][j] == 1:
            K = K + MONOMIALS[j]
    #check if it is a nonlinear invariant
    if is_nonlinear_invariant(S_BOX, K) is not True:
        print("Warning! "), (K.algebraic_normal_form()), ("is not a nonlinear invariant but it is got from the matrix")

if left_1_vector_solvable == 1:
    K = BooleanFunction(x0 + x0) # here "0"
    for j in range(NUM_MONOMIALS):
        if left_1_vector_sole[j] == 1:
            K = K + MONOMIALS[j]
    #check if it is a nonlinear invariant
    if is_nonlinear_invariant(S_BOX, K) is not True:
        print("Warning! "), (K.algebraic_normal_form()), ("is not a nonlinear invariant but it is got from the matrix")


ker_list = ker.list()
for i in range(len(ker_list)):
    K = BooleanFunction(x0 + x0) # here "0"
    for j in range(NUM_MONOMIALS):
        if ker_list[i][j] == 1:
            K = K + MONOMIALS[j]
    
    #check if it has the linear structure
    if K.has_linear_structure():
        NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE + 1
        #check if it is balanced
        if K.is_balanced():
            NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE +1

    if left_1_vector_solvable == 1:
        for j in range(NUM_MONOMIALS):
            if left_1_vector_sole[j] ==1:
                K = K + MONOMIALS[j]
        #check if it has the linear structure
        if K.has_linear_structure():
            NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE + 1
            #check if it is balanced
            if K.is_balanced():
                NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE +1

print ("== Nonlinear Invariants Info of %s" %ALG_NAME)
if left_1_vector_solvable:
    print ("Nonlinear invariants g such that g(x) + g(sbox(x)) = 1 are included in the left range.")
else:
    print ("Nonlinear invariants g such that g(x) + g(sbox(x)) = 1 are *NOT* included in the left range.")
print ("# of Nonlinear Invariants : %d" % NUM_NON_INVARIANT)
print ("# of Nonlinear Invariants with Linear Structure : %d" % NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE)
print ("# of Balanced Nonlinear Invariants with Linear Structure : %d" % NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE)