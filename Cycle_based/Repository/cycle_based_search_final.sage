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

def get_alg_degree_from_ANF(ANF_str):
    ANF_mono_list =  ANF_str.split(' + ')
    return ANF_mono_list[0].count('x')


set_sbox()


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
elif S_BOX_BIT_SIZE == 16:
    R.<x15,x14,x13,x12,x11,x10,x9,x8,x7,x6,x5,x4,x3,x2,x1,x0>=BooleanPolynomialRing(16)
    MONOMIALS = monomials([x15,x14,x13,x12,x11,x10,x9,x8,x7,x6,x5,x4,x3,x2,x1,x0],[2,2,2,2,2,2,2,2,2,2,2,2,2,2,2,2])
else:
    print("The bit size of the S-box is not supported")
    exit


TMP_S_BOX = range(S_BOX_CARDINALITY)
for i in range(len(S_BOX)):
    TMP_S_BOX[i] = S_BOX[i] + 1
P = Permutation(TMP_S_BOX)

CYCLES = P.to_cycles()
NUM_CYCLES = len(CYCLES)
CYCLE_LENGTHS = range(NUM_CYCLES)
AT_LEAST_ONE_ODD_FLAG = 0

for i in range(len(CYCLES)):
    CYCLES[i] = list(CYCLES[i])
    for j in range(len(CYCLES[i])):
        CYCLES[i][j] -=1 
    CYCLE_LENGTHS[i] = len(CYCLES[i])
    if (CYCLE_LENGTHS[i] & 0x1) != 0:
        AT_LEAST_ONE_ODD_FLAG = 1

print("The length of each cycle : "),(CYCLE_LENGTHS)

NUM_NON_INVARIANT = 0
NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = 0
NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = 0

NUM_EACH_DEG_NI = range(S_BOX_BIT_SIZE + 1)
NUM_EACH_DEG_NI_WITH_LS = range(S_BOX_BIT_SIZE + 1)
NUM_EACH_DEG_BNI_WITH_LS = range(S_BOX_BIT_SIZE + 1)

#init
for i in range(S_BOX_BIT_SIZE + 1):
    NUM_EACH_DEG_NI[i] = 0
    NUM_EACH_DEG_NI_WITH_LS[i] = 0
    NUM_EACH_DEG_BNI_WITH_LS[i] = 0


if AT_LEAST_ONE_ODD_FLAG == 1:
    NUM_NON_INVARIANT = 2**(NUM_CYCLES)
else:
    NUM_NON_INVARIANT = 2**(NUM_CYCLES + 1) 
    

_0_BASIS = range(NUM_CYCLES)
for i in range(NUM_CYCLES):
    Boolean_Table = range(S_BOX_CARDINALITY)
    for j in range(S_BOX_CARDINALITY):
        if j in CYCLES[i]:
            Boolean_Table[j] = 1
        else:
            Boolean_Table[j] = 0
    _0_BASIS[i] = BooleanFunction(Boolean_Table)
    if is_nonlinear_invariant(S_BOX, _0_BASIS[i]) is not True:
            print("Warning! "), (_0_BASIS[i].algebraic_normal_form()), ("is not a nonlinear invariant but it is got.")


i = 0
while i < 2**NUM_CYCLES:
    K = BooleanFunction(x0 + x0) # here "0"
    chosen_vec = list(format(i, 'b').zfill(NUM_CYCLES))
    for j in range(NUM_CYCLES):
        if chosen_vec[j] == '1':
            K = K + _0_BASIS[j]
    alg_deg = K.algebraic_degree()
    NUM_EACH_DEG_NI[alg_deg] += 1
    #check if it has the linear structure
    if K.has_linear_structure():
        NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE + 1
        NUM_EACH_DEG_NI_WITH_LS[alg_deg] += 1
        #check if it is balanced
        if K.is_balanced():
            NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE +1
            NUM_EACH_DEG_BNI_WITH_LS[alg_deg] += 1
    i = i + 1

print (i)

if AT_LEAST_ONE_ODD_FLAG == 0:
    i = 0
    while i < 2**NUM_CYCLES:
        Boolean_Table = range(S_BOX_CARDINALITY)
        start_bit_vec = list(format(i, 'b').zfill(NUM_CYCLES))
        for j in range(NUM_CYCLES):
            start_bit_vec[j] = int(start_bit_vec[j])
        for j in range(NUM_CYCLES):
            for k in CYCLES[j]:
                Boolean_Table[k] = start_bit_vec[j]
                start_bit_vec[j] = start_bit_vec[j] ^^ 1 #alternating
        K = BooleanFunction(Boolean_Table)
        alg_deg = K.algebraic_degree()
        NUM_EACH_DEG_NI[alg_deg] += 1
        #check if it has the linear structure
        if K.has_linear_structure():
            NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE + 1
            NUM_EACH_DEG_NI_WITH_LS[alg_deg] += 1
            #check if it is balanced
            if K.is_balanced():
                NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE = NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE +1
                NUM_EACH_DEG_BNI_WITH_LS[alg_deg] += 1
        i = i + 1
    

print ("== Nonlinear Invariants Info of %s" %ALG_NAME)
if AT_LEAST_ONE_ODD_FLAG == 0:
    print ("Every cycle has the even legnth.")
    print ("Therefore, nonlinear invariants g such that g(x) + g(sbox(x)) = 1 are included.")
else:
    print ("At least one cycle has the odd length.")
    print ("Therefore, nonlinear invariants g such that g(x) + g(sbox(x)) = 1 are *NOT* included.")

print ("# of Nonlinear Invariants : %d" % NUM_NON_INVARIANT)
for i in range(len(NUM_EACH_DEG_NI)):
    print("%d deg : %d" %(i,NUM_EACH_DEG_NI[i]))
print ("# of Nonlinear Invariants with Linear Structure : %d" % NUM_NON_INVARIANT_WITH_LINEAR_STRUCTURE)
for i in range(len(NUM_EACH_DEG_NI_WITH_LS)):
    print("%d deg : %d" %(i,NUM_EACH_DEG_NI_WITH_LS[i]))
print ("# of Balanced Nonlinear Invariants with Linear Structure : %d" % NUM_BALANCED_NON_INVARIANT_WITH_LINEAR_STRUCTURE)
for i in range(len(NUM_EACH_DEG_BNI_WITH_LS)):
    print("%d deg : %d" %(i,NUM_EACH_DEG_BNI_WITH_LS[i]))